import MiniForth.Divergence
import MiniForth.Grind.Rules

/-!
# Divergence: induction supplies what automation needs

The program `: FOREVER FOREVER ;` returns to the same configuration after every
step. The induction below covers every fuel budget. Interpreter completeness then
rules out every finite semantic derivation, including runtime errors.

We expose one recursive step explicitly; the automation rules never unfold
recursive dictionary entries on their own. The remaining proofs use the resulting
nontermination theorem as a local fact.

The interactive proof of `forever_no_eval` shows the logical bridge explicitly.
`use` instantiates only the listed rules; `→` selects a hypothesis as the trigger,
while `=` selects an equation's left-hand side. `cases_next` opens the sole
existential fact, providing the fuel witness. In the editor, `show_state` and
`show_cases` can inspect these stages without changing the proof.
-/

namespace MiniForth.Grind.Divergence

open Deep
open MiniForth.Divergence (forever foreverEnv)

/-- One step returns to the same code, leaving a smaller fuel budget. -/
theorem run_forever (fuel : Nat) (s : Stack) :
    run foreverEnv fuel forever s = none := by
  induction fuel with
  | zero => grind [run, runFrom, forever]
  | succ fuel ih =>
    change run foreverEnv fuel forever s = none
    grind

/-- Every finite derivation would produce its outcome with some fuel budget. -/
theorem forever_no_eval (s : Stack) (r : Result) :
    ¬ Eval foreverEnv forever s r := by
  grind only =>
    use [→ run_complete] -- A finite derivation supplies a fuel budget.
    cases_next          -- Extract that budget from the existential fact.
    use [= run_forever]  -- Every budget times out, contradicting completeness.

/-- No suffix can be reached, regardless of the stack or desired result. -/
theorem forever_append (rest : Body) : Equiv foreverEnv (forever ++ rest) forever := by
  grind [eval_append, forever_no_eval]

/-- An error is an observable outcome; divergence has no finite outcome. -/
theorem forever_not_equiv_drop : ¬ Equiv foreverEnv forever [.prim .drop] := by
  have failure : Eval foreverEnv [.prim .drop] [] (.error .stackUnderflow) := by grind
  grind [forever_no_eval]

end MiniForth.Grind.Divergence
