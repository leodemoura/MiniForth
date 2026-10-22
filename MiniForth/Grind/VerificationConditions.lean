import MiniForth.Grind.Tactics
import MiniForth.Syntax
import MiniForth.Divergence

/-!
# From Hoare triples to verification conditions

`forth_wp` calculates preconditions using proved WP rules. The remaining goal is
ordinary logic or arithmetic, which can be handled manually or with `grind`.
Trivial conditions may already be discharged by simplification.

Unknown stack shapes remain as matches, and symbolic flags remain as conditions.
Calls need an exact WP contract or an explicit unfolding step. A Hoare contract
only supplies a sufficient precondition; it is not an exact WP rewrite rule.
-/

namespace MiniForth.Grind.VerificationConditions

open Deep

/-- WP calculation leaves the arithmetic identity for the proof author. -/
example (n : Int) :
    Hoare env (fun s => s = [n + 1]) [forth| DUP *] (fun s => s = [n * n + 2 * n + 1]) := by
  forth_wp
  grind

/-- Stack requirements are part of the generated condition. -/
example (Q : Assertion) (s : Stack) :
    WP env [forth| DUP *] Q s ↔
      match s with
      | [] => False
      | n :: tail => Q (n * n :: tail) := by
  forth_wp
  rfl

/-- Both paths consume the flag, and the continuation runs after the chosen path. -/
example (Q : Assertion) (flag a b : Int) (tail : Stack) :
    WP env [forth| IF + ELSE SWAP - THEN 2 *] Q (flag :: b :: a :: tail) ↔
      if flag = 0 then Q ((b - a) * 2 :: tail)
      else Q ((a + b) * 2 :: tail) := by
  forth_wp

example : ¬ Hoare env (fun s => s = []) [forth| IF + ELSE THEN] (fun _ => True) := by
  forth_wp

example : ¬ Hoare env (fun s => s = [7]) [forth| +] (fun _ => True) := by
  forth_wp

/-- Prove a reusable call contract by unfolding the declaration once. -/
theorem square_call_wp (lookup : env "SQUARE" = some [forth| DUP *]) :
    WP env (.call "SQUARE" :: rest) Q s ↔
      match s with
      | [] => False
      | n :: tail => WP env rest Q (n * n :: tail) := by
  rw [wp_call lookup]
  forth_wp
  cases s <;> rfl

/-- The supplied contract lets WP calculation continue past the call. -/
example (lookup : env "SQUARE" = some [forth| DUP *]) (n : Int) :
    Hoare env (fun s => s = [n]) [forth| SQUARE 1 +] (fun s => s = [1 + n * n]) := by
  forth_wp [square_call_wp lookup]
  grind

open MiniForth.Divergence (forever foreverEnv forever_no_eval)

/-- A recursive call remains an obligation; the separate divergence proof settles it. -/
example : ¬ Hoare foreverEnv (fun s => s = []) forever (fun _ => True) := by
  forth_wp [forever]
  guard_target = ¬ WP foreverEnv [forth| FOREVER] (fun _ => True) []
  rintro ⟨t, he, _⟩
  exact forever_no_eval [] (.ok t) he

end MiniForth.Grind.VerificationConditions
