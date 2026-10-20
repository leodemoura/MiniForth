import MiniForth.Basic
import Lean

/-!
# Writing MiniForth inside Lean

These quotations expand into the ordinary syntax trees in `Basic`; parsing does
not execute a program. Brackets mark where the embedded language ends.

Names may contain hyphens, as in `SUM-OF-SQUARES`. A hyphen without surrounding
spaces belongs to a name; `-3` is a negative literal and `- 3` subtracts, then
pushes three. Declarations use Forth's `: NAME ... ;` syntax.

A bare name that resolves to a Lean local variable pushes its value as an `Int`;
other names call Forth words. `{term}` explicitly pushes a Lean expression, and
`CALL name` explicitly calls a word even when a Lean local has the same name.
Primitives keep their meaning, and declaration names always name Forth words.
-/

namespace MiniForth

open Lean

declare_syntax_cat forthName
syntax ident (noWs "-" noWs ident)* : forthName

declare_syntax_cat forthInstr
syntax num : forthInstr
syntax "-" noWs num : forthInstr
syntax "+" : forthInstr
syntax "-" : forthInstr
syntax "*" : forthInstr
syntax "DUP" : forthInstr
syntax "SWAP" : forthInstr
syntax "DROP" : forthInstr
syntax "=" : forthInstr
syntax "{" term "}" : forthInstr
syntax "CALL" forthName : forthInstr
syntax forthName : forthInstr
syntax "IF" forthInstr* "ELSE" forthInstr* "THEN" : forthInstr

declare_syntax_cat forthDecl
syntax ":" forthName forthInstr* ";" : forthDecl

syntax "[forth|" forthInstr* "]" : term
syntax "[forthDecl|" forthDecl "]" : term
syntax "[forthProgram|" forthDecl* forthInstr* "]" : term

private def nameString (stx : TSyntax `forthName) : String :=
  -- Forth's global names use their spelling, independently of Lean macro scopes.
  String.intercalate "-" <|
    stx.raw[0].getId.eraseMacroScopes.toString false ::
      stx.raw[1].getArgs.toList.map (fun part => part[1].getId.eraseMacroScopes.toString false)

macro "forthName%" name:forthName : term =>
  pure (quote (nameString name))

/-- Use Lean's hygienic local lookup, including section variables captured by a
quotation. Global Lean definitions do not change the meaning of bare Forth names. -/
private def isLocalValue (id : Ident) : Elab.Term.TermElabM Bool := do
  if let some (_, projections) ← resolveLocalName id.getId then
    return projections.isEmpty
  let .ident _ _ _ preresolved := id.raw | return false
  let sectionVars := (← read).sectionFVars
  return preresolved.any fun
    | .decl name [] => (sectionVars.find? name).isSome
    | _ => false

elab "forthNameInstr%" name:forthName : term => do
  let id : Ident := ⟨name.raw[0]⟩
  if name.raw[1].getArgs.isEmpty && (← isLocalValue id) then
    -- Preserve the identifier's binding and let Lean check its type normally.
    Elab.Term.elabTerm (← `(Instr.push $id)) none
  else
    Elab.Term.elabTerm (← `(Instr.call (forthName% $name))) none

macro "forthInstr%" instr:forthInstr : term =>
  match instr with
  | `(forthInstr| $n:num) => `(Instr.push $n)
  | `(forthInstr| -$n:num) => `(Instr.push (-$n))
  | `(forthInstr| +) => `(Instr.prim Prim.add)
  | `(forthInstr| -) => `(Instr.prim Prim.sub)
  | `(forthInstr| *) => `(Instr.prim Prim.mul)
  | `(forthInstr| DUP) => `(Instr.prim Prim.dup)
  | `(forthInstr| SWAP) => `(Instr.prim Prim.swap)
  | `(forthInstr| DROP) => `(Instr.prim Prim.drop)
  | `(forthInstr| =) => `(Instr.prim Prim.eq)
  | `(forthInstr| {$value:term}) => `(Instr.push $value)
  | `(forthInstr| CALL $name:forthName) => `(Instr.call (forthName% $name))
  | `(forthInstr| $name:forthName) => `(forthNameInstr% $name)
  | `(forthInstr| IF $yes:forthInstr* ELSE $no:forthInstr* THEN) =>
      `(Instr.branch [forth| $yes*] [forth| $no*])
  | _ => Macro.throwUnsupported

macro_rules
  | `([forth| $instr:forthInstr*]) => `([$[forthInstr% $instr],*])
  | `([forthDecl| : $name:forthName $instr:forthInstr* ;]) =>
      `(Decl.mk (forthName% $name) [forth| $instr*])
  | `([forthProgram| $decl:forthDecl* $instr:forthInstr*]) =>
      `(Program.mk [$[[forthDecl| $decl]],*] [forth| $instr*])

/-- The quotations expose ordinary constructors, so proofs can use `rfl`. -/
example : [forth| -3 DUP *] =
    [Instr.push (-3), Instr.prim .dup, Instr.prim .mul] := rfl

example : [forth| 5 2 - 3] =
    [Instr.push 5, Instr.push 2, Instr.prim .sub, Instr.push 3] := rfl

example : [forthDecl| : SUM-OF-SQUARES SQUARE SWAP SQUARE + ;] =
    Decl.mk "SUM-OF-SQUARES"
      [.call "SQUARE", .prim .swap, .call "SQUARE", .prim .add] := rfl

example : [forth| IF ELSE THEN] = [Instr.branch [] []] := rfl

-- Lean's escaped identifiers permit names outside the unquoted name grammar.
example : [forth| «SQUARE-2»] = [Instr.call "SQUARE-2"] := rfl

example : [forthProgram| : SQUARE DUP * ; 3 SQUARE] =
    Program.mk [Decl.mk "SQUARE" [.prim .dup, .prim .mul]]
      [.push 3, .call "SQUARE"] := rfl

-- Symbolic values are parameters of the syntax tree, not new runtime variables.
example (a b : Int) : [forth| a b +] = [.push a, .push b, .prim .add] := rfl
example (a b : Int) : [forth| {a + b} DUP] = [.push (a + b), .prim .dup] := rfl

-- Declarations and explicit calls keep their names even with a local collision.
example (SQUARE : Int) : [forthProgram| : SQUARE DUP * ; SQUARE CALL SQUARE] =
    Program.mk [Decl.mk "SQUARE" [.prim .dup, .prim .mul]]
      [.push SQUARE, .call "SQUARE"] := rfl

section
variable (a : Int)
example : [forth| a IF {a + 1} ELSE a THEN] =
    [.push a, .branch [.push (a + 1)] [.push a]] := rfl
end

example : (let a : Int := 7; [forth| a]) = [.push 7] := rfl

-- A global Lean definition is only a value when explicitly interpolated.
private def syntaxGlobal : Int := 11
example : [forth| syntaxGlobal {syntaxGlobal}] = [.call "syntaxGlobal", .push 11] := rfl

-- A local with the wrong type is an error, not an implicit fallback to a call.
#guard_msgs (drop info) in
#check_failure fun (a : Bool) => [forth| a]
example (_a : Bool) : [forth| CALL _a] = [Instr.call "_a"] := rfl

section
-- A macro's local binder must not capture a variable supplied by its caller.
local macro "forthScoped%" value:ident : term => do
  let name ← `(forthName| $value:ident)
  `(let a : Int := 99; [forth| $name:forthName])

example (a : Int) : forthScoped% a = [Instr.push a] := rfl

local macro "forthSquareCall%" : term => `([forth| SQUARE])
example : forthSquareCall% = [Instr.call "SQUARE"] := rfl
end

section
variable (captured : Int)
local macro "forthCaptured%" : term => `([forth| captured])
example : forthCaptured% = [Instr.push captured] := rfl
end

-- Parser regression checks: incomplete control flow, missing declaration
-- delimiters, stray control words, and unsupported instructions are errors.
run_elab do
  let env ← getEnv
  for source in ["[forth| IF 1 THEN]", "[forthProgram| : X 1 2]",
      "[forth| ELSE]", "[forth| /]"] do
    match Parser.runParserCategory env `term source with
    | .error _ => pure ()
    | .ok _ => throwError "malformed MiniForth unexpectedly parsed: {source}"

end MiniForth
