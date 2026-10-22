import MiniForth.Grind.Rules

/-!
# Small proof commands for MiniForth

`forth_unfold lookup` expands the leading call using a proof of its dictionary
entry. It performs exactly one call expansion, then normalizes list append.
Recursive calls in the resulting body remain available for a recursive contract.

`forth_wp` rewrites a Hoare triple or a WP goal into a verification condition.
It handles finite instruction sequences and conditionals, preserving stack
underflow as `False`. Calls remain as WP obligations unless an exact WP contract
is supplied with `forth_wp [contract]`. Additional arguments can also unfold
named program bodies or assertions.

To expand a call once, use `rw [wp_call lookup]` before `forth_wp`. Do not give
`wp_call lookup` for a recursive Forth program to the simplifier: it would keep
expanding the recursive call. Recursive proofs still need induction and a
termination argument.

These macros use syntax quotation and ordinary Lean tactics; they add no semantic
rules. Their expansions are deliberately short enough to inspect during the tutorial.
-/

namespace MiniForth.Grind

/-- Expand one leading call, using the supplied dictionary lookup proof. -/
macro "forth_unfold " lookup:term : tactic =>
  `(tactic|
    (rw [MiniForth.Deep.eval_call $lookup]
     simp only [List.nil_append, List.cons_append, List.append_nil]))

/-- Generate a verification condition, using optional definitions and exact WP contracts. -/
macro "forth_wp" " [" args:term,* "]" : tactic =>
  `(tactic|
    simp [MiniForth.Deep.Hoare, MiniForth.Deep.wp_append,
      MiniForth.Deep.wp_add, MiniForth.Deep.wp_sub, MiniForth.Deep.wp_mul,
      MiniForth.Deep.wp_dup, MiniForth.Deep.wp_swap, MiniForth.Deep.wp_drop,
      MiniForth.Deep.wp_eq, MiniForth.Deep.wp_branch_result, $[$args:term],*])

macro "forth_wp" : tactic => `(tactic| forth_wp [])

end MiniForth.Grind
