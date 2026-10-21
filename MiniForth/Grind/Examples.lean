import MiniForth.Grind.Rules
import MiniForth.Examples

/-!
# Program proofs using the annotated semantic interface

The arithmetic dictionary is shared with the original lesson. These proofs derive
its contracts again from the instruction semantics. The new continuation contracts
are registered locally: larger words can use them without expanding their bodies.
-/

namespace MiniForth.Grind.Examples

open Deep
open MiniForth.Examples (arithmetic)

theorem square_spec (n : Int) (s : Stack) :
    Eval env [forth| DUP *] (n :: s) (.ok (n * n :: s)) := by
  grind

/-- A reusable contract: SQUARE leaves every continuation the squared top value. -/
@[local grind =] theorem square_step (n : Int) (s : Stack) :
    Eval arithmetic.env (.call "SQUARE" :: rest) (n :: s) r ↔
      Eval arithmetic.env rest (n * n :: s) r := by
  rw [eval_call (env := arithmetic.env) (name := "SQUARE") rfl]
  grind

theorem square_call_spec (n : Int) (s : Stack) :
    Eval arithmetic.env [forth| SQUARE] (n :: s) (.ok (n * n :: s)) := by
  grind

/-- Open CUBE once, then use the SQUARE contract inside it. -/
@[local grind =] theorem cube_step (n : Int) (s : Stack) :
    Eval arithmetic.env (.call "CUBE" :: rest) (n :: s) r ↔
      Eval arithmetic.env rest (n * n * n :: s) r := by
  rw [eval_call (env := arithmetic.env) (name := "CUBE") rfl]
  grind

-- Compare two programs using the proved word contracts.
example (a : Int) : Equiv arithmetic.env [forth| a CUBE] [forth| a SQUARE a *] := by
  grind

theorem sumOfSquares_spec (a b : Int) (s : Stack) :
    Eval arithmetic.env [forth| SUM-OF-SQUARES] (b :: a :: s)
      (.ok ((a * a + b * b) :: s)) := by
  rw [eval_call (env := arithmetic.env) (name := "SUM-OF-SQUARES") rfl]
  grind

theorem arithmetic_result : Eval arithmetic.env arithmetic.main [] (.ok [25]) := by
  grind [arithmetic, sumOfSquares_spec]

/-- The induction follows the transformation; grind handles each local rewrite. -/
theorem constantFold_correct (code : Body) : Equiv env (constantFold code) code := by
  fun_induction constantFold code <;> grind [eval_cons]

example : Equiv arithmetic.env [forth| 7 SQUARE] [forth| 3 4 + SQUARE] := by
  grind [constantFold_correct, constantFold]

example : Equiv arithmetic.env [forth| 7 SQUARE SQUARE 3 +]
    [forth| 3 4 + SQUARE SQUARE 1 2 + +] := by
  -- Supply this instance directly instead of asking E-matching to discover it.
  grind [constantFold_correct (env := arithmetic.env)
    [forth| 3 4 + SQUARE SQUARE 1 2 + +], constantFold]

example : Equiv env [forth| DUP +] [forth| 2 *] := by
  grind

end MiniForth.Grind.Examples
