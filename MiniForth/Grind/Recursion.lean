import MiniForth.Grind.Tactics
import MiniForth.Recursion

/-!
# Induction with automated local reasoning

We still choose induction on the natural input and unfold one recursive call.
The `forth_unfold` macro makes that semantic choice explicit without repeating
the underlying rewrite and list simplification.

Here the finite instruction rules run in `grind`'s normalizer. That exposes the
prefix without spending E-matching rounds on each instruction. The local
annotations also normalize the two mathematical factorial equations and casts.
These equations reduce known natural-number constructors; they do not unfold
the recursive MiniForth dictionary.

The induction hypothesis supplies the successful recursive call. The guarded
multi-pattern from `Rules` then connects that contract to the remaining `*`.
`grind` handles the branch condition, intermediate stack, and arithmetic.
-/

namespace MiniForth.Grind.Recursion

open Deep MiniForth.Recursion

attribute [local grind norm] eval_push eval_prim eval_singleton exec_branch
attribute [local grind norm] fact.eq_1 fact.eq_2 Int.natCast_mul

theorem factorial_correct (n : Nat) (s : Stack) :
    Eval factorial.env [forth| FACT] ((n : Int) :: s) (.ok ((fact n : Int) :: s)) := by
  induction n generalizing s with
  | zero =>
    forth_unfold factorial_lookup
    grind
  | succ n ih =>
    forth_unfold factorial_lookup
    -- FACT on n preserves n + 1 for the multiplication after it returns.
    have recursive := ih ((n + 1 : Int) :: s)
    grind

theorem factorial_hoare (n : Nat) (s : Stack) :
    Hoare factorial.env (fun input => input = (n : Int) :: s)
      [forth| FACT] (fun output => output = (fact n : Int) :: s) := by
  grind [Hoare, WP, factorial_correct]

end MiniForth.Grind.Recursion
