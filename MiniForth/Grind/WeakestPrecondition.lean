import MiniForth.Grind.Rules
import MiniForth.Syntax
import MiniForth.Grind.Divergence

/-!
# Weakest preconditions with `grind`

Compare these contracts with `Examples.lean`. The semantic rules in `Rules.lean`
compute preconditions, and `grind` handles stack cases, existential witnesses,
and integer arithmetic. No theorem about a particular program is registered.

The last examples keep three notions separate: successful termination, absence
of runtime errors, and a postcondition conditional on successful termination.
-/

namespace MiniForth.Grind.WP

open Deep
open MiniForth.Divergence (forever foreverEnv)

/-- Automation discovers the required input slot as well as the output value. -/
theorem square_wp (Q : Assertion) (s : Stack) :
    WP env [forth| DUP *] Q s ↔ ∃ n rest, s = n :: rest ∧ Q (n * n :: rest) := by
  grind

/-- A Hoare triple specializes the exact precondition to a chosen input. -/
theorem square_hoare (n : Int) (rest : Stack) :
    Hoare env (fun s => s = n :: rest) [forth| DUP *]
      (fun s => s = n * n :: rest) := by
  grind [Hoare]

/-- Addition needs two operands; every unused stack slot is preserved. -/
theorem add_wp (Q : Assertion) (s : Stack) :
    WP env [forth| +] Q s ↔
      ∃ a b rest, s = b :: a :: rest ∧ Q ((a + b) :: rest) := by
  grind

/-- The intermediate postcondition is computed by the registered sequencing rules. -/
theorem add_three_wp (Q : Assertion) (n : Int) (s : Stack) :
    WP env [forth| 3 +] Q (n :: s) ↔ Q ((n + 3) :: s) := by
  grind

-- A liberal precondition alone says nothing about failing executions.
example : WLP emptyEnv [forth| DROP] (fun _ => False) [] := by
  grind [WLP]

example : ¬ SafeWLP emptyEnv [forth| DROP] (fun _ => True) [] := by
  have failure : Eval emptyEnv [forth| DROP] [] (.error .stackUnderflow) := by grind
  grind [SafeWLP, Safe]

-- The divergence theorem is proved separately by induction over fuel.
-- Once supplied, automation exposes the difference between partial and total correctness.
example : SafeWLP foreverEnv forever (fun _ => False) s := by
  grind [SafeWLP, Safe, WLP, Divergence.forever_no_eval]

example : ¬ WP foreverEnv forever (fun _ => True) s := by
  grind [Deep.WP, Divergence.forever_no_eval]

end MiniForth.Grind.WP
