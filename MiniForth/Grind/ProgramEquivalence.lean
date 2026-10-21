import MiniForth.Syntax
import MiniForth.Grind.Rules

/-!
# Program equivalence with `grind`

Compare these proofs with `MiniForth/ProgramEquivalence.lean`. The annotations in
`Rules` expose the stack semantics; `grind` then handles integer arithmetic and
equalities. The theorems still quantify over every initial stack and every result,
so they preserve runtime errors as well as successful values.
-/

namespace MiniForth.Grind.ProgramEquivalence

open Deep

theorem add_comm (env : Env) (a b : Int) :
    Equiv env [forth| a b +] [forth| b a +] := by
  grind

theorem mul_comm (env : Env) (a b : Int) :
    Equiv env [forth| a b *] [forth| b a *] := by
  grind

theorem add_assoc (env : Env) (a b c : Int) :
    Equiv env [forth| a b + c +] [forth| a b c + +] := by
  grind

theorem mul_add (env : Env) (a b c : Int) :
    Equiv env [forth| a b c + *] [forth| a b * a c * +] := by
  grind

theorem dup_expand (env : Env) (a : Int) :
    Equiv env [forth| a DUP *] [forth| a a *] := by
  grind

theorem push_drop (env : Env) (a : Int) :
    Equiv env [forth| a DROP] [forth|] := by
  grind

/-- Automatic case analysis covers the empty stack as well as nonempty stacks. -/
theorem add_offsets (env : Env) (a b : Int) :
    Equiv env [forth| a + b +] [forth| {a + b} +] := by
  grind -funext

/-- The sequencing rule lifts a proved equivalence into arbitrary surrounding code. -/
theorem add_comm_in_context (env : Env) (a b : Int) (before after : Body) :
    Equiv env (before ++ [forth| a b +] ++ after)
      (before ++ [forth| b a +] ++ after) := by
  grind [eval_append, add_comm]

/-- Equal operands make the false branch unreachable, for arbitrary branch bodies. -/
theorem select_equal (env : Env) (a b : Int) (yes no : Body) (h : a = b) :
    Equiv env ([forth| a b =] ++ [.branch yes no]) yes := by
  grind

/-- Supply the empty stack as a counterexample; automation checks its behavior. -/
theorem zero_add_not_equiv_nil (env : Env) :
    ¬ Equiv env [forth| 0 +] [forth|] := by
  intro h
  have he := h [] (.ok [])
  grind

end MiniForth.Grind.ProgramEquivalence
