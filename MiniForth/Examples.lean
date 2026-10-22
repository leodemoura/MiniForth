import MiniForth.Link
import MiniForth.Equivalence
import MiniForth.WeakestPrecondition
import MiniForth.Divergence

/-!
# Worked examples for the tutorial

Read the declarations first, then compare the same words in `Shallow.lean`.
Computed examples establish individual facts; the quantified theorems below
cover all integers and every untouched suffix of the input stack.
-/

namespace MiniForth.Examples

open Deep

def arithmetic : Program := [forthProgram|
  : SQUARE DUP * ;
  : CUBE DUP SQUARE * ;
  : SUM-OF-SQUARES SQUARE SWAP SQUARE + ;
  3 4 SUM-OF-SQUARES
]

#eval runMain arithmetic

theorem arithmetic_wellFormed : arithmetic.WellFormed := by
  simp [Program.WellFormed, arithmetic, Program.calls, Body.calls, Program.env]

-- A successful computation is also a proof about the fuel-independent semantics.
theorem arithmetic_result : Eval arithmetic.env arithmetic.main [] (.ok [25]) :=
  run_sound (fuel := 30) rfl

example : run arithmetic.env 30 [forth| 3 CUBE] = some (.ok [27]) := rfl

/-- A contract for every input and every unused stack suffix. -/
theorem square_spec (n : Int) (s : Stack) :
    Eval env [forth| DUP *] (n :: s) (.ok (n * n :: s)) :=
  square_correspondence.mpr rfl

/-- Calls can be unfolded using their dictionary entry, just as Lean unfolds a def. -/
theorem square_call_spec (n : Int) (s : Stack) :
    Eval arithmetic.env [forth| SQUARE] (n :: s) (.ok (n * n :: s)) := by
  apply (call_equiv (env := arithmetic.env) (name := "SQUARE") rfl _ _).mpr
  exact square_spec n s

theorem sumOfSquares_spec (a b : Int) (s : Stack) :
    Eval arithmetic.env [forth| SUM-OF-SQUARES] (b :: a :: s)
      (.ok ((a * a + b * b) :: s)) := by
  rw [eval_call (env := arithmetic.env) (name := "SUM-OF-SQUARES") rfl]
  change Eval arithmetic.env [forth| SQUARE SWAP SQUARE +] _ _
  rw [eval_call (env := arithmetic.env) (name := "SQUARE") rfl]
  simp only [List.cons_append, List.nil_append, eval_prim, Prim.eval]
  rw [eval_call (env := arithmetic.env) (name := "SQUARE") rfl]
  simp [eval_prim, Prim.eval, Int.add_comm]

-- The same nontrivial program, with names handled by Lean itself.
example (a b : Int) (s : Stack) :
    Shallow.sumOfSquares (b :: a :: s) = .ok ((a * a + b * b) :: s) :=
  Shallow.sumOfSquares_run a b s

/-- A transformation can inspect deep code. Its proof does not mention fuel. -/
example : constantFold [forth| 3 4 + SQUARE] = [forth| 7 SQUARE] := rfl

example : Equiv arithmetic.env [forth| 7 SQUARE] [forth| 3 4 + SQUARE] :=
  constantFold_correct [forth| 3 4 + SQUARE]

#eval constantFold [forth| 3 4 + SQUARE SQUARE 1 2 + +]

example : Equiv arithmetic.env [forth| 7 SQUARE SQUARE 3 +] [forth| 3 4 + SQUARE SQUARE 1 2 + +] :=
  constantFold_correct [forth| 3 4 + SQUARE SQUARE 1 2 + +]

-- Equivalent code can need different fuel: execution cost is not an outcome.
example : run emptyEnv 1 [forth| 3 4 +] = none := rfl
example : run emptyEnv 1 (constantFold [forth| 3 4 +]) = some (.ok [7]) := rfl

example : Equiv env [forth| DUP +] [forth| 2 *] := double_equiv

-- An attractive but unsound optimization: the empty input distinguishes them.
example : ¬ Equiv env [forth| SWAP SWAP] [forth|] := swap_swap_not_equiv_nil

/-- Work backwards through SQUARE: require a top element, then constrain its square. -/
theorem square_wp (Q : Assertion) (s : Stack) :
    WP env [forth| DUP *] Q s ↔ ∃ n rest, s = n :: rest ∧ Q (n * n :: rest) := by
  cases s <;> simp [wp_prim, Prim.eval] <;> grind

/-- This is a total-correctness Hoare triple, including absence of underflow. -/
theorem square_hoare (n : Int) (rest : Stack) :
    Hoare env (fun s => s = n :: rest) [forth| DUP *]
      (fun s => s = n * n :: rest) := by
  rintro s rfl
  exact (square_wp _ _).mpr ⟨n, rest, rfl, rfl⟩

/-- Both arithmetic and the minimum stack requirement emerge from the WP rules. -/
theorem add_wp (Q : Assertion) (s : Stack) :
    WP env [forth| +] Q s ↔
      ∃ a b rest, s = b :: a :: rest ∧ Q ((a + b) :: rest) := by
  cases s with
  | nil => simp [wp_prim, Prim.eval]
  | cons b s => cases s <;> simp [wp_prim, Prim.eval] <;> grind

/-- Postconditions flow backwards through a sequence. -/
theorem add_three_wp (Q : Assertion) (n : Int) (s : Stack) :
    WP env [forth| 3 +] Q (n :: s) ↔ Q ((n + 3) :: s) := by
  simp [wp_prim, Prim.eval]

-- Liberal partial correctness alone is vacuous when execution fails.
example : WLP emptyEnv [forth| DROP] (fun _ => False) [] := by
  intro t ht
  simp [Prim.eval] at ht

example : ¬ SafeWLP emptyEnv [forth| DROP] (fun _ => True) [] := by
  rintro ⟨hsafe, _⟩
  apply hsafe .stackUnderflow
  exact .consError .prim

-- Real divergence is proved for every execution, not inferred from one timeout.
example : SafeWLP Divergence.foreverEnv Divergence.forever (fun _ => False) s := by
  constructor
  · intro e
    exact Divergence.forever_no_eval s (.error e)
  · intro t h
    exact False.elim (Divergence.forever_no_eval s (.ok t) h)

example : ¬ WP Divergence.foreverEnv Divergence.forever (fun _ => True) s := by
  rintro ⟨t, ht, _⟩
  exact Divergence.forever_no_eval s (.ok t) ht

end MiniForth.Examples
