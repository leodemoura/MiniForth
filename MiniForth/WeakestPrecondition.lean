import MiniForth.Deep

/-!
# Weakest preconditions

`WP code Q` asks for successful termination in a state satisfying `Q`. Thus stack
underflow, an unknown word, and divergence all fail this *total correctness* contract.
Fuel is an execution aid, and does not appear in the specification.
-/

namespace MiniForth.Deep

abbrev Assertion := Stack → Prop

/-- Total correctness: execution succeeds and establishes the postcondition. -/
def WP (env : Env) (code : Body) (Q : Assertion) : Assertion := fun s =>
  ∃ t, Eval env code s (.ok t) ∧ Q t

def Hoare (env : Env) (P : Assertion) (code : Body) (Q : Assertion) : Prop :=
  ∀ s, P s → WP env code Q s

/-- A liberal precondition constrains successful outcomes only. By itself it
allows both runtime errors and divergence. -/
def WLP (env : Env) (code : Body) (Q : Assertion) : Assertion := fun s =>
  ∀ t, Eval env code s (.ok t) → Q t

/-- Safety excludes finite executions that end in a runtime error. -/
def Safe (env : Env) (code : Body) : Assertion := fun s =>
  ∀ e, ¬ Eval env code s (.error e)

/-- Safe partial correctness still permits divergence. -/
def SafeWLP (env : Env) (code : Body) (Q : Assertion) : Assertion := fun s =>
  Safe env code s ∧ WLP env code Q s

/-- Every sufficient precondition implies WP; WP itself is sufficient. -/
theorem wp_weakest : Hoare env P code Q ↔ ∀ s, P s → WP env code Q s :=
  Iff.rfl

theorem wp_valid : Hoare env (WP env code Q) code Q :=
  fun _ h => h

theorem wp_mono (h : ∀ s, Q s → R s) : ∀ s, WP env code Q s → WP env code R s := by
  rintro s ⟨t, ht, hQ⟩
  exact ⟨t, ht, h t hQ⟩

@[simp] theorem wp_nil : WP env [] Q s ↔ Q s := by
  constructor
  · rintro ⟨t, h, ht⟩
    cases h
    exact ht
  · intro h
    exact ⟨s, .nil, h⟩

/-- Work backwards: the precondition for `b` becomes the postcondition for `a`. -/
theorem wp_append {a b : Body} : WP env (a ++ b) Q s ↔ WP env a (WP env b Q) s := by
  constructor
  · rintro ⟨t, h, ht⟩
    rcases eval_append.mp h with ⟨u, ha, hb⟩ | ⟨e, _, he⟩
    · exact ⟨u, ha, t, hb, ht⟩
    · cases he
  · rintro ⟨u, ha, t, hb, ht⟩
    exact ⟨t, eval_append.mpr (Or.inl ⟨u, ha, hb⟩), ht⟩

theorem hoare_seq {a b : Body} (ha : Hoare env P a R) (hb : Hoare env R b Q) : Hoare env P (a ++ b) Q := by
  intro s hs
  apply wp_append.mpr
  exact wp_mono hb s (ha s hs)

theorem hoare_consequence (hP : ∀ s, P' s → P s)
    (h : Hoare env P code Q) (hQ : ∀ s, Q s → Q' s)
    : Hoare env P' code Q' := by
  intro s hs
  exact wp_mono hQ s (h s (hP s hs))

/-- A single instruction must succeed before its continuation can run. -/
theorem wp_cons : WP env (i :: rest) Q s ↔ ∃ t, Exec env i s (.ok t) ∧ WP env rest Q t := by
  constructor
  · rintro ⟨u, h, hu⟩
    cases h with
    | consOk hi hr => exact ⟨_, hi, u, hr, hu⟩
  · rintro ⟨t, hi, u, hr, hu⟩
    exact ⟨u, .consOk hi hr, hu⟩

@[simp] theorem wp_push : WP env (.push n :: rest) Q s ↔ WP env rest Q (n :: s) := by
  rw [wp_cons]
  constructor
  · rintro ⟨t, hi, ht⟩
    cases hi
    exact ht
  · intro h
    exact ⟨_, .push, h⟩

theorem wp_prim : WP env (.prim op :: rest) Q s ↔ ∃ t, op.eval s = .ok t ∧ WP env rest Q t := by
  rw [wp_cons]
  constructor
  · rintro ⟨t, hi, ht⟩
    generalize hresult : Except.ok t = result at hi
    cases hi
    exact ⟨t, hresult.symm, ht⟩
  · rintro ⟨t, hi, ht⟩
    exact ⟨t, by simpa only [hi] using (Exec.prim (env := env) (op := op) (s := s)), ht⟩

theorem wp_call (lookup : env name = some body) : WP env (.call name :: rest) Q s ↔ WP env body (WP env rest Q) s := by
  rw [wp_cons]
  constructor
  · rintro ⟨t, hi, ht⟩
    cases hi with
    | call he hb =>
      cases Option.some.inj (he.symm.trans lookup)
      exact ⟨t, hb, ht⟩
  · rintro ⟨t, hb, ht⟩
    exact ⟨t, .call lookup hb, ht⟩

@[simp] theorem wp_branch_zero
    : WP env (.branch yes no :: rest) Q (0 :: s) ↔ WP env no (WP env rest Q) s := by
  rw [wp_cons]
  constructor
  · rintro ⟨t, hi, ht⟩
    cases hi with
    | branchZero hb => exact ⟨t, hb, ht⟩
    | branchNonzero hn _ => exact False.elim (hn rfl)
  · rintro ⟨t, hb, ht⟩
    exact ⟨t, .branchZero hb, ht⟩

theorem wp_branch_nonzero (hn : n ≠ 0)
    : WP env (.branch yes no :: rest) Q (n :: s) ↔ WP env yes (WP env rest Q) s := by
  rw [wp_cons]
  constructor
  · rintro ⟨t, hi, ht⟩
    cases hi with
    | branchZero _ => exact False.elim (hn rfl)
    | branchNonzero _ hb => exact ⟨t, hb, ht⟩
  · rintro ⟨t, hb, ht⟩
    exact ⟨t, .branchNonzero hn hb, ht⟩

@[simp] theorem wp_branch_empty : ¬ WP env (.branch yes no :: rest) Q [] := by
  rw [wp_cons]
  rintro ⟨t, hi, _⟩
  cases hi

theorem wp_equiv {a b : Body} (h : Equiv env a b) : WP env a Q s ↔ WP env b Q s := by
  unfold Equiv at h
  simp only [WP, h]

/-- Determinism connects existential total correctness to all-outcome safety. -/
theorem wp_implies_safeWLP : WP env code Q s → SafeWLP env code Q s := by
  rintro ⟨t, ht, hQ⟩
  constructor
  · intro e he
    cases eval_deterministic ht he
  · intro u hu
    cases eval_deterministic ht hu
    exact hQ

end MiniForth.Deep
