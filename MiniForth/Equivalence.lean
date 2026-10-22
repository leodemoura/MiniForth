import MiniForth.Deep
import MiniForth.Shallow

/-!
# Equivalence and a verified transformation

Deep syntax gives us something to inspect and rewrite. The constant folder below
traverses one instruction sequence; it leaves declarations and the bodies of
conditional instructions alone. Its correctness theorem quantifies over every
environment, input stack, and result, including errors.
-/

namespace MiniForth.Deep

@[simp] theorem exec_push : Exec env (.push n) s r ↔ r = .ok (n :: s) := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .push

@[simp] theorem exec_prim : Exec env (.prim op) s r ↔ r = op.eval s := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .prim

@[simp] theorem eval_push : Eval env (.push n :: rest) s r ↔
    Eval env rest (n :: s) r := by
  simp [eval_cons]

@[simp] theorem eval_prim : Eval env (.prim op :: rest) s r ↔
    match op.eval s with
    | .ok t => Eval env rest t r
    | .error e => r = .error e := by
  rw [eval_cons]
  cases h : op.eval s <;> simp [h]

@[simp] theorem eval_singleton : Eval env [i] s r ↔ Exec env i s r := by
  cases r <;> simp [eval_cons]

theorem exec_call (h : env name = some body) :
    Exec env (.call name) s r ↔ Eval env body s r := by
  constructor
  · intro he
    cases he with
    | call h' hb =>
      cases Option.some.inj (h.symm.trans h')
      exact hb
    | unknown h' => simp [h] at h'
  · exact .call h

/-- Unfold a call while preserving its continuation and error propagation. -/
theorem eval_call (h : env name = some body) :
    Eval env (.call name :: rest) s r ↔ Eval env (body ++ rest) s r := by
  simp only [eval_cons, exec_call h, eval_append]

@[refl] theorem Equiv.refl (code : Body) : Equiv env code code := fun _ _ => Iff.rfl

@[symm] theorem Equiv.symm {a b : Body} (h : Equiv env a b) : Equiv env b a :=
  fun s r => (h s r).symm

theorem Equiv.trans {a b c : Body} (h₁ : Equiv env a b) (h₂ : Equiv env b c) :
    Equiv env a c := fun s r => (h₁ s r).trans (h₂ s r)

theorem Equiv.append {a b c d : Body} (h₁ : Equiv env a b) (h₂ : Equiv env c d) :
    Equiv env (a ++ c) (b ++ d) := by
  unfold Equiv at h₁ h₂ ⊢
  intro s r
  simp only [eval_append, h₁, h₂]

theorem Equiv.cons {a b : Body} (h : Equiv env a b) (i : Instr) : Equiv env (i :: a) (i :: b) := by
  unfold Equiv at h ⊢
  intro s r
  simp only [eval_cons, h]

/-- Inlining preserves behavior because lookup uses the same global dictionary. -/
theorem call_equiv (h : env name = some body) : Equiv env [.call name] body := by
  intro s r
  rw [eval_singleton, exec_call h]

/-- Fold adjacent literal additions; recurse over the remaining sequence. -/
def constantFold : Body → Body
  | .push a :: .push b :: .prim .add :: rest => .push (a + b) :: constantFold rest
  | i :: rest => i :: constantFold rest
  | [] => []

theorem constantFold_correct (code : Body) : Equiv env (constantFold code) code := by
  fun_induction constantFold code with
  | case1 a b rest ih =>
    intro s r
    simpa only [eval_push, eval_prim, Prim.eval] using ih ((a + b) :: s) r
  | case2 i rest _ ih => exact ih.cons i
  | case3 => exact Equiv.refl []

/-- SWAP SWAP is an identity when the two required stack slots exist. -/
theorem swap_swap_iff (a b : Int) (s : Stack) :
    Eval env [.prim .swap, .prim .swap] (a :: b :: s) r ↔
      r = .ok (a :: b :: s) := by
  simp [eval_prim, Prim.eval]

/-- Removing SWAP SWAP without a stack precondition loses underflow behavior. -/
theorem swap_swap_not_equiv_nil : ¬ Equiv env [.prim .swap, .prim .swap] [] := by
  intro h
  have he := (h [] (.ok [])).mpr Eval.nil
  simp [eval_prim, Prim.eval] at he

/-- The arithmetic equivalence also holds on stacks that cause underflow. -/
theorem double_equiv : Equiv env [.prim .dup, .prim .add] [.push 2, .prim .mul] := by
  intro s r
  cases s with
  | nil => simp [eval_prim, Prim.eval]
  | cons a s =>
    have h : a + a = a * 2 := by omega
    simp [eval_prim, Prim.eval, h]

/-- Both embeddings give SQUARE the same meaning, including stack underflow. -/
theorem square_correspondence :
    Eval env [.prim .dup, .prim .mul] s r ↔ Shallow.square s = r := by
  cases s <;> simp [eval_prim, Prim.eval, Shallow.square, Shallow.seq,
    Shallow.dup, Shallow.mul, Shallow.bin, eq_comm]

example : constantFold [.push 3, .push 4, .prim .add, .call "SQUARE"] =
    [.push 7, .call "SQUARE"] := rfl

end MiniForth.Deep
