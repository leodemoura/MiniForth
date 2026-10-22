import MiniForth.Basic

/-!
# Deep embedding

Forth programs are data. Big-step semantics describes finite
executions; a computation that runs forever has no big-step derivation.
-/

namespace MiniForth.Deep

mutual
  inductive Exec (env : Env) : Instr → Stack → Result → Prop where
    | push : Exec env (.push n) s (.ok (n :: s))
    | prim : Exec env (.prim op) s (op.eval s)
    | call : env name = some body → Eval env body s r → Exec env (.call name) s r
    | unknown : env name = none → Exec env (.call name) s (.error (.unknownWord name))
    | branchZero : Eval env no s r → Exec env (.branch yes no) (0 :: s) r
    | branchNonzero : n ≠ 0 → Eval env yes s r → Exec env (.branch yes no) (n :: s) r
    | branchUnderflow : Exec env (.branch yes no) [] (.error .stackUnderflow)

  inductive Eval (env : Env) : Body → Stack → Result → Prop where
    | nil : Eval env [] s (.ok s)
    | consOk : Exec env i s (.ok t) → Eval env rest t r → Eval env (i :: rest) s r
    | consError : Exec env i s (.error e) → Eval env (i :: rest) s (.error e)
end

@[simp] theorem eval_nil : Eval env [] s r ↔ r = .ok s := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem eval_cons : Eval env (i :: rest) s r ↔
    (∃ t, Exec env i s (.ok t) ∧ Eval env rest t r) ∨
    (∃ e, Exec env i s (.error e) ∧ r = .error e) := by
  constructor
  · intro h
    cases h with
    | consOk hi hr => exact .inl ⟨_, hi, hr⟩
    | consError hi => exact .inr ⟨_, hi, rfl⟩
  · rintro (⟨t, hi, hr⟩ | ⟨e, hi, rfl⟩)
    · exact .consOk hi hr
    · exact .consError hi

/-- Sequential composition propagates failures and continues after success. -/
theorem eval_append {a b : Body} : Eval env (a ++ b) s r ↔
    (∃ t, Eval env a s (.ok t) ∧ Eval env b t r) ∨
    (∃ e, Eval env a s (.error e) ∧ r = .error e) := by
  induction a generalizing s r with
  | nil => simp
  | cons i a ih =>
    constructor
    · intro h
      cases h with
      | consError hi => exact .inr ⟨_, .consError hi, rfl⟩
      | consOk hi hr =>
        rcases ih.mp hr with ⟨t, ha, hb⟩ | ⟨e, ha, rfl⟩
        · exact .inl ⟨t, .consOk hi ha, hb⟩
        · exact .inr ⟨e, .consOk hi ha, rfl⟩
    · rintro (⟨t, ha, hb⟩ | ⟨e, ha, rfl⟩)
      · cases ha with
        | consOk hi hr => exact .consOk hi (ih.mpr (.inl ⟨_, hr, hb⟩))
      · cases ha with
        | consError hi => exact .consError hi
        | consOk hi hr => exact .consOk hi (ih.mpr (.inr ⟨_, hr, rfl⟩))

/-- The observable behavior includes both successful stacks and runtime errors. -/
def Equiv (env : Env) (a b : Body) : Prop :=
  ∀ s r, Eval env a s r ↔ Eval env b s r

/-- A running configuration contains the entire remaining instruction sequence. -/
inductive Config where
  | run (code : Body) (stack : Stack)
  | error (error : RuntimeError)
  deriving Repr

/-- A successful terminal configuration has no instructions left. -/
def terminal : Result → Config
  | .ok s => .run [] s
  | .error e => .error e

/-- One machine transition. Calls and conditionals expose their selected code. -/
inductive Step (env : Env) : Config → Config → Prop where
  | push : Step env (.run (.push n :: rest) s) (.run rest (n :: s))
  | primOk : op.eval s = .ok t →
      Step env (.run (.prim op :: rest) s) (.run rest t)
  | primError : op.eval s = .error e →
      Step env (.run (.prim op :: rest) s) (.error e)
  | call : env name = some body →
      Step env (.run (.call name :: rest) s) (.run (body ++ rest) s)
  | unknown : env name = none →
      Step env (.run (.call name :: rest) s) (.error (.unknownWord name))
  | branchZero : Step env (.run (.branch yes no :: rest) (0 :: s)) (.run (no ++ rest) s)
  | branchNonzero : n ≠ 0 →
      Step env (.run (.branch yes no :: rest) (n :: s)) (.run (yes ++ rest) s)
  | branchUnderflow : Step env (.run (.branch yes no :: rest) []) (.error .stackUnderflow)

/-- Zero or more small steps. -/
inductive Steps (env : Env) : Config → Config → Prop where
  | refl : Steps env c c
  | step : Step env c d → Steps env d e → Steps env c e

theorem Steps.trans (h₁ : Steps env c d) (h₂ : Steps env d e) : Steps env c e := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

private def Config.append (c : Config) (rest : Body) : Config :=
  match c with
  | .run code s => .run (code ++ rest) s
  | .error e => .error e

private theorem Step.append (h : Step env c d) :
    Step env (c.append rest) (d.append rest) := by
  cases h <;> simp only [Config.append, List.cons_append, List.append_assoc] <;> constructor <;> assumption

private theorem Steps.append (h : Steps env c d) :
    Steps env (c.append rest) (d.append rest) := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step h.append ih

theorem eval_steps (h : Eval env code s r) :
    Steps env (.run code s) (terminal r) := by
  induction h using Eval.rec
      (motive_1 := fun i s r _ => Steps env (.run [i] s) (terminal r)) with
  | nil => exact .refl
  | @consOk i s t rest r hi hr ihI ihR =>
    have h := ihI.append (rest := rest)
    simp only [Config.append, List.singleton_append, terminal, List.nil_append] at h
    exact h.trans ihR
  | @consError i s e rest hi ihI =>
    have h := ihI.append (rest := rest)
    simpa only [Config.append, List.singleton_append, terminal] using h
  | push => exact .step .push .refl
  | prim =>
    cases he : Prim.eval _ _ with
    | ok t => exact .step (.primOk he) .refl
    | error e => exact .step (.primError he) .refl
  | call he hb ih =>
    apply Steps.step (.call he)
    simpa only [List.append_nil] using ih
  | unknown he => exact .step (.unknown he) .refl
  | branchZero hb ih =>
    apply Steps.step .branchZero
    simpa only [List.append_nil] using ih
  | branchNonzero hn hb ih =>
    apply Steps.step (.branchNonzero hn)
    simpa only [List.append_nil] using ih
  | branchUnderflow => exact .step .branchUnderflow .refl

/-- Extend big-step evaluation to machine configurations. -/
private def Config.Denotes (c : Config) (env : Env) (r : Result) : Prop :=
  match c with
  | .run code s => Eval env code s r
  | .error e => r = .error e

private theorem step_eval (h : Step env c d) (hd : d.Denotes (env := env) r) :
    c.Denotes (env := env) r := by
  cases h with
  | push => exact .consOk .push hd
  | primOk he =>
    exact .consOk (by rw [← he]; exact .prim) hd
  | primError he =>
    cases hd
    exact .consError (by rw [← he]; exact .prim)
  | call he =>
    rcases eval_append.mp hd with ⟨t, ha, hb⟩ | ⟨e, ha, rfl⟩
    · exact .consOk (.call he ha) hb
    · exact .consError (.call he ha)
  | unknown he =>
    cases hd
    exact .consError (.unknown he)
  | branchZero =>
    rcases eval_append.mp hd with ⟨t, ha, hb⟩ | ⟨e, ha, rfl⟩
    · exact .consOk (.branchZero ha) hb
    · exact .consError (.branchZero ha)
  | branchNonzero hn =>
    rcases eval_append.mp hd with ⟨t, ha, hb⟩ | ⟨e, ha, rfl⟩
    · exact .consOk (.branchNonzero hn ha) hb
    · exact .consError (.branchNonzero hn ha)
  | branchUnderflow =>
    cases hd
    exact .consError .branchUnderflow

private theorem steps_denotes (h : Steps env c d) (hd : d.Denotes (env := env) r) :
    c.Denotes (env := env) r := by
  induction h with
  | refl => exact hd
  | step h _ ih => exact step_eval h (ih hd)

theorem steps_eval (h : Steps env (.run code s) (terminal r)) : Eval env code s r := by
  apply steps_denotes h
  cases r with
  | ok t => exact .nil
  | error e => rfl

/-- Big and small steps agree on every finite outcome, including runtime errors. -/
theorem eval_iff_steps : Eval env code s r ↔ Steps env (.run code s) (terminal r) :=
  ⟨eval_steps, steps_eval⟩

theorem eval_deterministic (h₁ : Eval env code s r₁) (h₂ : Eval env code s r₂) : r₁ = r₂ := by
  induction h₁ using Eval.rec
      (motive_1 := fun i s r _ => ∀ r', Exec env i s r' → r = r') generalizing r₂ with
  | nil => cases h₂; rfl
  | consOk hi hr ihI ihR =>
    cases h₂ with
    | consOk hi₂ hr₂ =>
      cases ihI _ hi₂
      exact ihR hr₂
    | consError hi₂ => cases ihI _ hi₂
  | consError hi ihI =>
    cases h₂ with
    | consOk hi₂ hr₂ => cases ihI _ hi₂
    | consError hi₂ => exact ihI _ hi₂
  | push => rename_i r' h; cases h; rfl
  | prim => rename_i r' h; cases h; rfl
  | call he hb ih =>
    rename_i r' h
    cases h with
    | call he₂ hb₂ =>
      cases Option.some.inj (he.symm.trans he₂)
      exact ih hb₂
    | unknown he₂ => simp [he] at he₂
  | unknown he =>
    rename_i r' h
    cases h with
    | call he₂ hb₂ => simp [he] at he₂
    | unknown => rfl
  | branchZero hb ih =>
    rename_i r' h
    cases h with
    | branchZero hb₂ => exact ih hb₂
    | branchNonzero hn hb₂ => exact False.elim (hn rfl)
  | branchNonzero hn hb ih =>
    rename_i r' h
    cases h with
    | branchZero hb₂ => exact False.elim (hn rfl)
    | branchNonzero hn₂ hb₂ => exact ih hb₂
  | branchUnderflow => rename_i r' h; cases h; rfl

/-- Compute the unique next state of a nonterminal configuration. -/
def transition (env : Env) (i : Instr) (rest : Body) (s : Stack) : Config :=
  match i with
  | .push n => .run rest (n :: s)
  | .prim op => match op.eval s with
    | .ok t => .run rest t
    | .error e => .error e
  | .call name => match env name with
    | some body => .run (body ++ rest) s
    | none => .error (.unknownWord name)
  | .branch yes no => match s with
    | [] => .error .stackUnderflow
    | n :: t => .run ((if n = 0 then no else yes) ++ rest) t

theorem step_transition : Step env (.run (i :: rest) s) (transition env i rest s) := by
  cases i with
  | push => exact .push
  | prim op =>
    cases he : op.eval s with
    | ok t => simpa only [transition, he] using Step.primOk (env := env) (rest := rest) he
    | error e => simpa only [transition, he] using Step.primError (env := env) (rest := rest) he
  | call name =>
    cases he : env name with
    | none => simpa only [transition, he] using Step.unknown (s := s) (rest := rest) he
    | some body => simpa only [transition, he] using Step.call (s := s) (rest := rest) he
  | branch yes no =>
    cases s with
    | nil => exact .branchUnderflow
    | cons n s =>
      by_cases hn : n = 0
      · subst n
        simpa [transition] using Step.branchZero (env := env) (yes := yes) (no := no) (rest := rest) (s := s)
      · simpa [transition, hn] using Step.branchNonzero (env := env) (yes := yes) (no := no) (rest := rest) (s := s) hn

theorem transition_of_step (h : Step env (.run (i :: rest) s) d) :
    transition env i rest s = d := by
  cases h <;> simp_all [transition]

/-- Fuel counts machine transitions. A final configuration needs no fuel. -/
def runFrom (env : Env) : Nat → Config → Option Result
  | _, .run [] s => some (.ok s)
  | _, .error e => some (.error e)
  | 0, .run (_ :: _) _ => none
  | fuel + 1, .run (i :: rest) s => runFrom env fuel (transition env i rest s)

/-- `none` means exhausted fuel, not a runtime error or a proof of divergence. -/
def run (env : Env) (fuel : Nat) (code : Body) (s : Stack := []) : Option Result :=
  runFrom env fuel (.run code s)

def runMain (p : Program) : Option Result :=
  run p.env 10000 p.main

theorem runFrom_sound (h : runFrom env fuel c = some r) : Steps env c (terminal r) := by
  induction fuel generalizing c with
  | zero =>
    cases c with
    | error e => cases h; exact .refl
    | run code s =>
      cases code with
      | nil => cases h; exact .refl
      | cons => contradiction
  | succ fuel ih =>
    cases c with
    | error e => cases h; exact .refl
    | run code s =>
      cases code with
      | nil => cases h; exact .refl
      | cons i rest => exact .step step_transition (ih h)

theorem runFrom_complete (h : Steps env c (terminal r)) :
    ∃ fuel, runFrom env fuel c = some r := by
  generalize he : terminal r = d at h
  induction h with
  | refl =>
    rw [← he]
    exact ⟨0, by cases r <;> rfl⟩
  | @step c d e hs h ih =>
    obtain ⟨fuel, hf⟩ := ih he
    cases c with
    | error e => cases hs
    | run code s =>
      cases code with
      | nil => cases hs
      | cons i rest =>
        refine ⟨fuel + 1, ?_⟩
        simpa only [runFrom, transition_of_step hs] using hf

theorem run_sound (h : run env fuel code s = some r) : Eval env code s r :=
  steps_eval (runFrom_sound h)

/-- Every finite derivation can be reproduced by the interpreter with enough fuel. -/
theorem run_complete (h : Eval env code s r) : ∃ fuel, run env fuel code s = some r :=
  runFrom_complete (eval_steps h)

theorem eval_iff_run : Eval env code s r ↔ ∃ fuel, run env fuel code s = some r :=
  ⟨run_complete, fun ⟨_, h⟩ => run_sound h⟩

end MiniForth.Deep
