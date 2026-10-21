import MiniForth.Grind.Rules

/-!
# Small proof commands for MiniForth

`forth_unfold lookup` expands the leading call using a proof of its dictionary
entry. It performs exactly one call expansion, then normalizes list append.
Recursive calls in the resulting body remain available for a recursive contract.

This macro uses syntax quotation and ordinary Lean tactics; it adds no semantic
rule. Its expansion is deliberately short enough to inspect during the course.
-/

namespace MiniForth.Grind

/-- Expand one leading call, using the supplied dictionary lookup proof. -/
macro "forth_unfold " lookup:term : tactic =>
  `(tactic|
    (rw [MiniForth.Deep.eval_call $lookup]
     simp only [List.nil_append, List.cons_append, List.append_nil]))

end MiniForth.Grind
