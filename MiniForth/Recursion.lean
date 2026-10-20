import MiniForth.Equivalence
import MiniForth.Link
import MiniForth.WeakestPrecondition

/-!
# Terminating recursion

The deep language permits recursion independently of Lean's termination checker.
We establish termination of this particular program by induction on its input.
The proof preserves an arbitrary stack suffix, so FACT can be used inside other
words. The natural-number precondition matters: negative integers do not reach
zero by repeatedly subtracting one.
-/

namespace MiniForth.Recursion

open Deep

def factorial : Program := [forthProgram|
  : FACT
      DUP 0 =
      IF DROP 1
      ELSE DUP 1 - FACT *
      THEN ;
  5 FACT
]

/-- The usual mathematical factorial; Lean's standard library has no factorial
function, so we give its two defining equations here. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem factorial_lookup : factorial.env "FACT" =
    some [forth| DUP 0 = IF DROP 1 ELSE DUP 1 - FACT * THEN] := rfl

theorem factorial_wellFormed : factorial.WellFormed := by
  simp [Program.WellFormed, factorial, Program.calls, Body.calls, Program.env]

/-- FACT terminates on every natural input and preserves the rest of the stack. -/
theorem factorial_correct (n : Nat) (s : Stack) :
    Eval factorial.env [forth| FACT] ((n : Int) :: s) (.ok ((fact n : Int) :: s)) := by
  induction n generalizing s with
  | zero =>
    rw [eval_singleton, exec_call factorial_lookup]
    simp only [eval_prim, eval_push, Prim.eval, Int.natCast_zero, fact,
      Int.natCast_one, ↓reduceIte, eval_singleton]
    apply Exec.branchNonzero (by decide)
    simp [eval_prim, Prim.eval]
  | succ n ih =>
    rw [eval_singleton, exec_call factorial_lookup]
    have hn : (n.succ : Int) ≠ 0 := by omega
    simp only [eval_prim, eval_push, Prim.eval, hn, ↓reduceIte, eval_singleton]
    apply Exec.branchZero
    simp only [eval_prim, eval_push, Prim.eval, Int.natCast_succ, Int.add_sub_cancel]
    apply Eval.consOk (eval_singleton.mp (ih ((n + 1 : Int) :: s)))
    simp [Prim.eval, fact, Int.natCast_mul, Int.natCast_succ]

/-- This is a total-correctness contract: the recursive word must return. -/
theorem factorial_hoare (n : Nat) (s : Stack) :
    Hoare factorial.env (fun input => input = (n : Int) :: s)
      [forth| FACT] (fun output => output = (fact n : Int) :: s) := by
  rintro input rfl
  exact ⟨_, factorial_correct n s, rfl⟩

/-- Executing a concrete program is useful feedback, separate from the proof
above, which covers every natural input and every stack suffix. -/
example : run factorial.env 100 factorial.main [] = some (.ok [120]) := by rfl

example : Eval factorial.env factorial.main [] (.ok [120]) := by
  exact run_sound (fuel := 100) (by rfl)

end MiniForth.Recursion
