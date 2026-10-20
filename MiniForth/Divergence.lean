import MiniForth.Deep

/-!
# A timeout is not a nontermination proof

Both a finite computation and an infinite computation can exhaust a fuel budget.
To establish divergence, we prove that *every* budget is exhausted, then use the
interpreter's completeness theorem. No special divergence constructor is added
to the big-step semantics: its derivations describe finite computations.
-/

namespace MiniForth.Divergence

open Deep

/-- The mathematical version of `: FOREVER FOREVER ;`. -/
def forever : Body := [.call "FOREVER"]

def foreverEnv : Env := fun name =>
  if name = "FOREVER" then some forever else none

/-- Every step returns to precisely the same configuration. -/
theorem forever_step (s : Stack) :
    Step foreverEnv (.run forever s) (.run forever s) := by
  exact .call (name := "FOREVER") (body := forever) (rest := []) rfl

/-- This argument quantifies over all fuel budgets, not just one test run. -/
theorem run_forever (fuel : Nat) (s : Stack) :
    run foreverEnv fuel forever s = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

/-- The recursive word produces neither a value nor a runtime error. -/
theorem forever_no_eval (s : Stack) (r : Result) :
    ¬ Eval foreverEnv forever s r := by
  intro h
  obtain ⟨fuel, hf⟩ := run_complete h
  rw [run_forever] at hf
  contradiction

/-- Code after an infinite loop is unreachable. -/
theorem forever_append (rest : Body) : Equiv foreverEnv (forever ++ rest) forever := by
  intro s r
  constructor
  · intro h
    rcases eval_append.mp h with ⟨t, ha, _⟩ | ⟨e, ha, _⟩
    · exact False.elim (forever_no_eval s (.ok t) ha)
    · exact False.elim (forever_no_eval s (.error e) ha)
  · intro h
    exact False.elim (forever_no_eval s r h)

/-- Explicit error outcomes keep a failing program distinct from a diverging one. -/
theorem forever_not_equiv_drop : ¬ Equiv foreverEnv forever [.prim .drop] := by
  intro h
  have failure : Eval foreverEnv [.prim .drop] [] (.error .stackUnderflow) :=
    .consError .prim
  exact forever_no_eval [] (.error .stackUnderflow) ((h [] _).mpr failure)

/-- Exhausting a particular budget does not establish nontermination. -/
example : run emptyEnv 0 [.push 1] [] = none := rfl
example : run emptyEnv 1 [.push 1] [] = some (.ok [1]) := rfl

/-- Runtime failure is a different result from fuel exhaustion. -/
example : run emptyEnv 1 [.call "MISSING"] [] =
    some (.error (.unknownWord "MISSING")) := rfl

end MiniForth.Divergence
