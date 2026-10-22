import MiniForth.Equivalence
import MiniForth.Syntax

/-!
# From deeply embedded to shallowly embedded Forth programs

`denote prog code` interprets a Forth program using the shallow combinators.
The supplied `prog` maps names to shallowly embedded Forth programs, represented
by Lean functions. We traverse the syntax,
including both branches of a conditional, but do not look up or unfold declarations.

The correspondence theorem assumes that these Forth programs agree with calls in the
deep environment. Since a `Shallow.Prog` returns a result on every stack, this
assumption cannot hold for an environment containing a call that diverges.
-/

namespace MiniForth.Deep

open Shallow

/-- Map each primitive to its independently defined shallow implementation. -/
def denotePrim : Prim → Prog
  | .add  => add
  | .sub  => sub
  | .mul  => mul
  | .dup  => dup
  | .swap => swap
  | .drop => drop
  | .eq   => eq

/-- Interpret Forth programs compositionally; the caller supplies the meaning of names. -/
def denote (prog : String → Prog) : Body → Prog
  | []                     => skip
  | .push n :: rest        => push n >>> denote prog rest
  | .prim op :: rest       => denotePrim op >>> denote prog rest
  | .call name :: rest     => prog name >>> denote prog rest
  | .branch yes no :: rest => branch (denote prog yes) (denote prog no) >>> denote prog rest

/-- This includes stacks with too few operands. -/
theorem denotePrim_correct (op : Prim) (s : Stack) : denotePrim op s = op.eval s := by
  cases op <;> cases s with
  | nil => rfl
  | cons a rest => cases rest <;> rfl

/-- Concatenating Forth programs becomes composition of their shallow implementations. -/
theorem denote_append (prog : String → Prog) (a b : Body) :
    denote prog (a ++ b) = denote prog a >>> denote prog b := by
  induction a with
  | nil => simp [denote]
  | cons i rest ih => cases i <;> simp [denote, ih, Shallow.seq_assoc]

/-- Every supplied Forth program agrees with the corresponding deep call, including errors. -/
def CallsAgree (env : Env) (prog : String → Prog) : Prop :=
  ∀ name s r, Exec env (.call name) s r ↔ prog name s = r

private theorem eval_seq
    (hi : Exec env i s (p s)) (hr : ∀ t, Eval env rest t (q t)) :
    Eval env (i :: rest) s ((p >>> q) s) := by
  cases h : p s with
  | ok t =>
    simp only [Shallow.seq, h]
    exact .consOk (h ▸ hi) (hr t)
  | error e =>
    simp only [Shallow.seq, h]
    exact .consError (h ▸ hi)

/-- The translated Forth program's result has a finite big-step derivation. -/
theorem eval_denote (hprog : CallsAgree env prog) (code : Body) (s : Stack) :
    Eval env code s (denote prog code s) := by
  fun_induction denote prog code generalizing s with
  | case1 => exact .nil
  | case2 n rest ih => exact .consOk .push (ih _)
  | case3 op rest ih =>
    apply eval_seq (p := denotePrim op) (q := denote prog rest) _ ih
    rw [denotePrim_correct]
    exact .prim
  | case4 name rest ih =>
    exact eval_seq ((hprog name s _).mpr rfl) ih
  | case5 yes no rest ihYes ihNo ihRest =>
    apply eval_seq (p := Shallow.branch (denote prog yes) (denote prog no))
      (q := denote prog rest) _ ihRest
    cases s with
    | nil => exact .branchUnderflow
    | cons flag s =>
      by_cases h : flag = 0
      · subst flag
        exact .branchZero (ihNo s)
      · simpa [Shallow.branch, h] using Exec.branchNonzero h (ihYes s)

/-- The deeply and shallowly embedded Forth programs agree on every result. -/
theorem denote_correct (hprog : CallsAgree env prog) :
    Eval env code s r ↔ denote prog code s = r := by
  constructor
  · exact eval_deterministic (eval_denote hprog code s)
  · rintro rfl
    exact eval_denote hprog code s

/-- Under the call contract, equivalence of Forth programs is exactly function equality. -/
theorem equiv_iff_denote_eq (hprog : CallsAgree env prog) {a b : Body} :
    Equiv env a b ↔ denote prog a = denote prog b := by
  constructor
  · intro h
    funext s
    exact (denote_correct hprog).mp ((h s _).mpr (eval_denote hprog b s))
  · intro h s r
    rw [denote_correct hprog, denote_correct hprog, h]

/-! The translation exposes the shallow structure without executing the Forth program. -/

example : denote prog [forth| DUP *] = square := by
  simp [denote, denotePrim, Shallow.square]

example : denote prog [forth| IF + ELSE THEN] = branch add skip := by
  simp [denote, denotePrim]

example (a b : Int) : denote prog [forth| a b +] = push a >>> push b >>> add := by
  simp [denote, denotePrim]

namespace DenoteExamples

/-- A dictionary of shallowly embedded Forth programs; unknown names produce an error. -/
def prog : String → Shallow.Prog
  | "SQUARE" => Shallow.square
  | name => fun _ => .error (.unknownWord name)

def env : Env
  | "SQUARE" => some [forth| DUP *]
  | _ => none

theorem calls_agree : CallsAgree env prog := by
  intro name s r
  by_cases h : name = "SQUARE"
  · subst name
    exact (exec_call (env := env) rfl).trans square_correspondence
  · have lookup : env name = none := by simp [env]
    have meaning : prog name s = .error (.unknownWord name) := by simp [prog]
    rw [meaning]
    constructor
    · intro he
      cases he with
      | call he _ => simp [lookup] at he
      | unknown => rfl
    · rintro rfl
      exact .unknown lookup

example : denote prog [forth| DUP SQUARE *] = Shallow.cube := by
  simp [denote, denotePrim, prog, Shallow.cube]

example : denote prog [forth| 3 4 SQUARE SWAP SQUARE +] [] = .ok [25] := by cbv
example : denote prog [forth| SQUARE] [] = .error .stackUnderflow := by cbv
example : denote prog [forth| MISSING] [] = .error (.unknownWord "MISSING") := by cbv
example : denote prog [forth| IF + ELSE THEN] [0] = .ok [] := by cbv
example : denote prog [forth| IF + ELSE THEN] [-1] = .error .stackUnderflow := by cbv
example : denote prog [forth| IF + ELSE THEN] [-7, 20, 10, 99] = .ok [30, 99] := by cbv
example : denote prog [forth| IF MISSING ELSE THEN] [0] = .ok [] := by cbv

/-- Reuse a shallow equality to prove equivalence of deeply embedded Forth programs. -/
example : Equiv env [forth| DUP +] [forth| 2 *] := by
  apply (equiv_iff_denote_eq calls_agree).mpr
  simpa [denote, denotePrim] using Shallow.double_eq

end DenoteExamples

end MiniForth.Deep
