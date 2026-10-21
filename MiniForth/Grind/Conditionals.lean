import MiniForth.Conditionals
import MiniForth.Grind.Rules

/-!
# Conditional verification with `grind`

These are new proofs of the examples in `Conditionals.lean`, using its program
definitions. `grind` splits on the flag and stack shape, so the exact precondition
still admits `[0]` even though addition would need two more operands.

The local unfolding annotations expose the shallow functions. The deep proofs
use the generic semantic rules from `Rules.lean` and explicitly expose `body`.
-/

namespace MiniForth.Grind.Conditionals

open Deep
open MiniForth.Conditionals (addWhen body program)

attribute [local grind unfold] addWhen Shallow.branch Shallow.add Shallow.skip

theorem addWhen_zero (s : Stack) : addWhen (0 :: s) = .ok s := by
  grind

theorem addWhen_nonzero (h : flag ≠ 0) (a b : Int) (s : Stack) :
    addWhen (flag :: b :: a :: s) = .ok ((a + b) :: s) := by
  grind

theorem correspondence : Eval env body s r ↔ addWhen s = r := by
  grind [body]

/-- Dictionary lookup is supplied explicitly, keeping recursive unfolding controlled. -/
theorem call_correspondence :
    Eval program.env [forth| ADD-WHEN] s r ↔ addWhen s = r := by
  have lookup : program.env "ADD-WHEN" = some body := rfl
  grind [exec_call lookup, body]

/-- Both the arithmetic result and the branch-dependent stack requirement are exact. -/
theorem wp_exact (Q : Assertion) (s : Stack) : WP env body Q s ↔
    match s with
    | [] => False
    | flag :: rest =>
      if flag = 0 then Q rest
      else ∃ a b tail, rest = b :: a :: tail ∧ Q ((a + b) :: tail) := by
  grind [body]

/-- The rewrite preserves every outcome, including underflow in either program. -/
theorem flipped_equiv : Equiv env body [forth| 0 = IF ELSE + THEN] := by
  grind [body]

/-- In the zero branch, replacing the old value by `1` is the same as incrementing it.
`grind` combines the branch condition with arithmetic to remove the conditional.
The equivalence also covers the shared underflow on an empty input stack. -/
theorem conditional_increment :
    Equiv env [forth| DUP IF 1 + ELSE DROP 1 THEN] [forth| 1 +] := by
  grind

-- These are derived directly from the semantic rules, without using `wp_exact`.
example : WP emptyEnv body (fun s => s = []) [0] := by
  grind [body]

example : ¬ WP emptyEnv body (fun _ => True) [-1] := by
  grind [body]

end MiniForth.Grind.Conditionals
