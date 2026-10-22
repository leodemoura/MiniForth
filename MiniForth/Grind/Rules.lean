import MiniForth.Equivalence
import MiniForth.WeakestPrecondition

/-!
# An opt-in automation interface

The annotations expose finite instruction sequences and primitive stack operations
to `grind`. Recursive calls are unfolded explicitly at the use site: automatically
expanding a recursive dictionary would create an unbounded search.

`[grind norm]` normalizes primitive applications before proof search. The primitive
equations expose one stack slot at a time and keep underflow explicit.
`[grind unfold]` expands definitions during preprocessing. `[grind =]` instantiates
an equation when its left-hand side occurs; here that removes a known instruction.
`[grind .]` selects the application in the negative empty-stack rule as its trigger.
The custom `grind_pattern` for calls decomposes the finite instruction sequence;
its `=?=` constraint keeps it from competing with the primitive equations.
No program-specific correctness theorem is registered in this shared interface.

Import this module for the automated exercises; the original lessons keep their
step-by-step proofs and do not depend on these annotations.
-/

namespace MiniForth

namespace Prim

/-- Expose one stack slot at a time, including every underflow case. -/
@[grind norm] theorem eval_add : Prim.add.eval s =
    match s with
    | [] => .error .stackUnderflow
    | b :: tail => match tail with
      | [] => .error .stackUnderflow
      | a :: rest => .ok ((a + b) :: rest) := by
  cases s with
  | nil => rfl
  | cons b tail => cases tail <;> rfl

@[grind norm] theorem eval_sub : Prim.sub.eval s =
    match s with
    | [] => .error .stackUnderflow
    | b :: tail => match tail with
      | [] => .error .stackUnderflow
      | a :: rest => .ok ((a - b) :: rest) := by
  cases s with
  | nil => rfl
  | cons b tail => cases tail <;> rfl

@[grind norm] theorem eval_mul : Prim.mul.eval s =
    match s with
    | [] => .error .stackUnderflow
    | b :: tail => match tail with
      | [] => .error .stackUnderflow
      | a :: rest => .ok (a * b :: rest) := by
  cases s with
  | nil => rfl
  | cons b tail => cases tail <;> rfl

@[grind norm] theorem eval_dup : Prim.dup.eval s =
    match s with
    | [] => .error .stackUnderflow
    | a :: rest => .ok (a :: a :: rest) := by
  cases s <;> rfl

@[grind norm] theorem eval_swap : Prim.swap.eval s =
    match s with
    | [] => .error .stackUnderflow
    | b :: tail => match tail with
      | [] => .error .stackUnderflow
      | a :: rest => .ok (a :: b :: rest) := by
  cases s with
  | nil => rfl
  | cons b tail => cases tail <;> rfl

@[grind norm] theorem eval_drop : Prim.drop.eval s =
    match s with
    | [] => .error .stackUnderflow
    | _ :: rest => .ok rest := by
  cases s <;> rfl

@[grind norm] theorem eval_eq : Prim.eq.eval s =
    match s with
    | [] => .error .stackUnderflow
    | b :: tail => match tail with
      | [] => .error .stackUnderflow
      | a :: rest => .ok ((if a = b then -1 else 0) :: rest) := by
  cases s with
  | nil => rfl
  | cons b tail => cases tail <;> rfl

end Prim

namespace Shallow

/-- Normalize the independent shallow operation one stack slot at a time. -/
@[grind norm] theorem bin_result (op : Int → Int → Int) (s : Stack) : bin op s =
    match s with
    | [] => .error .stackUnderflow
    | b :: tail => match tail with
      | [] => .error .stackUnderflow
      | a :: rest => .ok (op a b :: rest) := by
  cases s with
  | nil => rfl
  | cons b tail => cases tail <;> rfl

end Shallow

namespace Deep

attribute [grind =] eval_nil eval_push eval_prim eval_singleton exec_push exec_prim
attribute [grind =] wp_nil wp_push wp_branch_zero wp_branch_nonzero
attribute [grind .] wp_branch_empty
attribute [grind unfold] Equiv

/-- A known instruction result determines the intermediate stack. -/
theorem eval_cons_of_exec_ok (h : Exec env i s (.ok t)) :
    Eval env (i :: rest) s r ↔ Eval env rest t r := by
  have unique (r' : Result) (h' : Exec env i s r') : r' = .ok t :=
    eval_deterministic (eval_singleton.mpr h') (eval_singleton.mpr h)
  grind [eval_cons]

-- Both terms must be present, and the instruction contract must be known true.
-- Merely mentioning a successful execution does not establish that it happens.
grind_pattern eval_cons_of_exec_ok => Exec env i s (.ok t), Eval env (i :: rest) s r where
  guard Exec env i s (.ok t)

-- Decompose a call followed by a continuation, without expanding its definition.
grind_pattern eval_cons => Eval env (i :: rest) s r where
  i =?= .call _

/-- The computed primitive result supplies the intermediate stack directly. -/
@[grind =] theorem wp_prim_result : WP env (.prim op :: rest) Q s ↔
    match op.eval s with
    | .ok t => WP env rest Q t
    | .error _ => False := by
  rw [wp_prim]
  cases h : op.eval s <;> simp

/-! These equations expose stack requirements directly for WP simplification. -/

theorem wp_add : WP env (.prim .add :: rest) Q s ↔
    match s with
    | b :: a :: tail => WP env rest Q ((a + b) :: tail)
    | _ => False := by
  cases s with
  | nil => simp [wp_prim_result, Prim.eval]
  | cons b tail => cases tail <;> simp [wp_prim_result, Prim.eval]

theorem wp_sub : WP env (.prim .sub :: rest) Q s ↔
    match s with
    | b :: a :: tail => WP env rest Q ((a - b) :: tail)
    | _ => False := by
  cases s with
  | nil => simp [wp_prim_result, Prim.eval]
  | cons b tail => cases tail <;> simp [wp_prim_result, Prim.eval]

theorem wp_mul : WP env (.prim .mul :: rest) Q s ↔
    match s with
    | b :: a :: tail => WP env rest Q (a * b :: tail)
    | _ => False := by
  cases s with
  | nil => simp [wp_prim_result, Prim.eval]
  | cons b tail => cases tail <;> simp [wp_prim_result, Prim.eval]

theorem wp_dup : WP env (.prim .dup :: rest) Q s ↔
    match s with
    | [] => False
    | a :: tail => WP env rest Q (a :: a :: tail) := by
  cases s <;> simp [wp_prim_result, Prim.eval]

theorem wp_swap : WP env (.prim .swap :: rest) Q s ↔
    match s with
    | b :: a :: tail => WP env rest Q (a :: b :: tail)
    | _ => False := by
  cases s with
  | nil => simp [wp_prim_result, Prim.eval]
  | cons b tail => cases tail <;> simp [wp_prim_result, Prim.eval]

theorem wp_drop : WP env (.prim .drop :: rest) Q s ↔
    match s with
    | [] => False
    | _ :: tail => WP env rest Q tail := by
  cases s <;> simp [wp_prim_result, Prim.eval]

theorem wp_eq : WP env (.prim .eq :: rest) Q s ↔
    match s with
    | b :: a :: tail => WP env rest Q ((if a = b then -1 else 0) :: tail)
    | _ => False := by
  cases s with
  | nil => simp [wp_prim_result, Prim.eval]
  | cons b tail => cases tail <;> simp [wp_prim_result, Prim.eval]

/-- Compute both conditional preconditions while retaining the flag test. -/
theorem wp_branch_result : WP env (.branch yes no :: rest) Q s ↔
    match s with
    | [] => False
    | flag :: tail =>
        if flag = 0 then WP env no (WP env rest Q) tail
        else WP env yes (WP env rest Q) tail := by
  cases s with
  | nil => simp
  | cons flag tail =>
    by_cases h : flag = 0
    · subst flag
      simp
    · simp [h, wp_branch_nonzero h]

/-- A conditional exposes just the selected branch and consumes its flag. -/
@[grind =] theorem exec_branch : Exec env (.branch yes no) s r ↔
    match s with
    | [] => r = .error .stackUnderflow
    | flag :: rest => if flag = 0 then Eval env no rest r else Eval env yes rest r := by
  cases s with
  | nil =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact .branchUnderflow
  | cons flag rest =>
    by_cases h : flag = 0
    · subst flag
      simp only [ite_true]
      constructor
      · intro he
        cases he with
        | branchZero hb => exact hb
        | branchNonzero hn _ => exact False.elim (hn rfl)
      · exact Exec.branchZero
    · simp only [h, ite_false]
      constructor
      · intro he
        cases he with
        | branchZero _ => exact False.elim (h rfl)
        | branchNonzero _ hb => exact hb
      · exact Exec.branchNonzero h

end Deep
end MiniForth
