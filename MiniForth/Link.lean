import MiniForth.Syntax

/-!
# Resolving declarations

MiniForth uses a global dictionary: declaration order does not matter, and both
forward references and recursive calls are allowed. Every declaration must have
a distinct name, and every call must resolve, including calls in branches that
might never execute. Linking does not claim that execution terminates or that
there are enough stack operands.
-/

namespace MiniForth

inductive LinkError where
  | duplicateWord (name : String)
  | unknownWord (name : String)
  deriving Repr, DecidableEq

/-- All names called by a body, including both sides of each conditional. -/
def Body.calls : Body → List String
  | [] => []
  | .push _ :: rest => Body.calls rest
  | .prim _ :: rest => Body.calls rest
  | .call name :: rest => name :: Body.calls rest
  | .branch yes no :: rest => Body.calls yes ++ Body.calls no ++ Body.calls rest

private def checkNames : List String → Except LinkError Unit
  | [] => .ok ()
  | name :: rest =>
      if name ∈ rest then .error (.duplicateWord name)
      else checkNames rest

private def checkCalls (env : Env) : List String → Except LinkError Unit
  | [] => .ok ()
  | name :: rest =>
      match env name with
      | none => .error (.unknownWord name)
      | some _ => checkCalls env rest

/-- Calls in declaration bodies, followed by calls in main. -/
def Program.calls (p : Program) : List String :=
  p.decls.flatMap (fun d => d.body.calls) ++ p.main.calls

/-- Linking checks names only: it does not imply termination or stack safety. -/
def Program.WellFormed (p : Program) : Prop :=
  (p.decls.map Decl.name).Nodup ∧ ∀ name ∈ p.calls, p.env name ≠ none

/-- Validate all declarations and main, then return their global dictionary. -/
def Program.link (p : Program) : Except LinkError Env := do
  checkNames (p.decls.map Decl.name)
  checkCalls p.env p.calls
  return p.env

private theorem checkNames_ok_iff (names : List String) :
    checkNames names = .ok () ↔ names.Nodup := by
  induction names with
  | nil => simp [checkNames]
  | cons name rest ih =>
      by_cases h : name ∈ rest <;> simp [checkNames, h, ih]

private theorem checkCalls_ok_iff (env : Env) (names : List String) :
    checkCalls env names = .ok () ↔ ∀ name ∈ names, env name ≠ none := by
  induction names with
  | nil => simp [checkCalls]
  | cons name rest ih =>
      cases h : env name <;> simp [checkCalls, h, ih]

/-- The executable linker exactly implements the stated name-resolution policy. -/
theorem Program.link_ok_iff (p : Program) (env : Env) :
    p.link = .ok env ↔ p.WellFormed ∧ env = p.env := by
  unfold Program.WellFormed
  rw [← checkNames_ok_iff, ← checkCalls_ok_iff]
  cases hn : checkNames (p.decls.map Decl.name) with
  | error e => simp [Program.link, hn, bind, Except.bind]
  | ok value =>
      cases value
      cases hc : checkCalls p.env p.calls with
      | error e => simp [Program.link, hn, hc, bind, Except.bind]
      | ok value =>
          cases value
          simp [Program.link, hn, hc, bind, Except.bind, pure, Except.pure, eq_comm]

-- Successful linking preserves the same dictionary used by the semantics.
#guard match [forthProgram| : SQUARE DUP * ; 3 SQUARE].link with
  | .ok env => env "SQUARE" == some [forth| DUP *]
  | .error _ => false

-- Global linking permits forward references and recursion.
#guard [forthProgram|
  : CUBE DUP SQUARE * ;
  : SQUARE DUP * ;
  3 CUBE
].link.toOption.isSome

#guard [forthProgram| : FOREVER FOREVER ; FOREVER].link.toOption.isSome

-- Repeated names are rejected, even when their bodies are identical.
#guard match [forthProgram| : X 1 ; : X 1 ;].link with
  | .error (.duplicateWord "X") => true
  | _ => false

#guard match [forthProgram| MISSING].link with
  | .error (.unknownWord "MISSING") => true
  | _ => false

-- Every declaration and nested branch is checked, including unused words.
#guard match [forthProgram|
  : UNUSED IF 1 ELSE IF ELSE MISSING THEN THEN ;
  42
].link with
  | .error (.unknownWord "MISSING") => true
  | _ => false

end MiniForth
