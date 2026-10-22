import MiniForth.Link
import MiniForth.Deep

/-!
# What successful linking guarantees at runtime

All calls in main and every declaration are checked, including nested branches.
This invariant is preserved when execution enters a called word or a branch.
Consequently a linked program cannot encounter an unknown word. It may still
underflow its stack or run forever.
-/

namespace MiniForth

open Deep

variable {p : Program}

private def Resolved (env : Env) (code : Body) : Prop :=
  ∀ name ∈ code.calls, env name ≠ none

private theorem resolved_cons :
    Resolved env (i :: rest) ↔ Resolved env [i] ∧ Resolved env rest := by
  cases i <;> simp [Resolved, Body.calls, or_imp, forall_and, and_assoc]

private theorem resolved_branch :
    Resolved env [.branch yes no] ↔ Resolved env yes ∧ Resolved env no := by
  simp [Resolved, Body.calls, or_imp, forall_and]

private theorem prim_no_unknown (op : Prim) (s : Stack) (name : String) :
    op.eval s ≠ .error (.unknownWord name) := by
  cases op <;> cases s with
  | nil => simp [Prim.eval]
  | cons a rest => cases rest <;> simp [Prim.eval]

private theorem eval_no_unknown
    (henv : ∀ name body, env name = some body → Resolved env body)
    (h : Eval env code s r) :
    Resolved env code → ∀ name, r ≠ .error (.unknownWord name) := by
  induction h using Eval.rec
      (motive_1 := fun i _ r _ => Resolved env [i] →
        ∀ name, r ≠ .error (.unknownWord name)) with
  | nil => exact fun _ _ h => nomatch h
  | consOk _ _ _ ihR =>
      intro hc
      exact ihR (resolved_cons.mp hc).2
  | consError _ ihI =>
      intro hc
      exact ihI (resolved_cons.mp hc).1
  | push => exact fun h => nomatch h
  | prim => exact prim_no_unknown _ _ _
  | call lookup _ ih =>
      rename_i hc name
      exact ih (henv _ _ lookup) name
  | @unknown missing _ lookup hc _ =>
      exact False.elim (hc missing (by simp [Body.calls]) lookup)
  | branchZero _ ih =>
      rename_i hc name
      exact ih (resolved_branch.mp hc).2 name
  | branchNonzero _ _ ih =>
      rename_i hc name
      exact ih (resolved_branch.mp hc).1 name
  | branchUnderflow => exact fun h => nomatch h

private theorem resolved_main (h : p.WellFormed) : Resolved p.env p.main := by
  intro name hn
  exact h.2 name (List.mem_append_right _ hn)

private theorem resolved_lookup (h : p.WellFormed)
    (lookup : p.env name = some body) : Resolved p.env body := by
  unfold Program.env at lookup
  cases hf : p.decls.find? (fun d => d.name == name) with
  | none => simp [hf] at lookup
  | some decl =>
      simp only [hf, Option.some.injEq] at lookup
      subst body
      intro called hc
      apply h.2 called
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨decl, List.mem_of_find?_eq_some hf, hc⟩

/-- Name validation rules out unknown-word failures on every input stack. -/
theorem Program.WellFormed.no_unknown (h : p.WellFormed) (s : Stack) (name : String) :
    ¬ Eval p.env p.main s (.error (.unknownWord name)) := by
  intro he
  exact eval_no_unknown (fun _ _ lookup => resolved_lookup h lookup) he
    (resolved_main h) name rfl

/-- The executable linker's accepted dictionary enjoys the same guarantee. -/
theorem Program.link_no_unknown {env : Env} (h : p.link = .ok env)
    (s : Stack) (name : String) :
    ¬ Eval env p.main s (.error (.unknownWord name)) := by
  obtain ⟨hwf, rfl⟩ := (Program.link_ok_iff p env).mp h
  exact hwf.no_unknown s name

end MiniForth
