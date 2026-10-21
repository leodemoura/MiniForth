import MiniForth.Syntax
import MiniForth.Equivalence

/-!
Regression tests for the Forth pretty printer. Round trips go through the printed
text, its parser, and its elaborator, so these also check whitespace and binding.
-/

namespace MiniForth.PrettyPrinterTests

open Lean Elab Command Term Meta

/-- Check both readable notation and preservation of the elaborated expression. -/
private def checkRoundTrip (term : Syntax) (expected : String) : TermElabM Unit := do
  let original ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  if original.hasMVar then
    throwError "round-trip test contains unresolved metavariables"
  let formatted ← PrettyPrinter.ppExpr original
  let printed := formatted.pretty
  unless (printed.splitOn expected).length > 1 do
    throwError "expected printed text to contain {expected.quote}, got:\n{printed}"
  -- Narrow widths exercise line breaks inside branches and declarations too.
  for width in [120, 30, 10] do
    let printed := formatted.pretty width
    let parsed ← match Parser.runParserCategory (← getEnv) `term printed with
      | .ok parsed => pure parsed
      | .error message => throwError "printed term did not parse:\n{printed}\n{message}"
    let restored ← elabTermEnsuringType parsed (some (← inferType original))
    synthesizeSyntheticMVarsNoPostponing
    let restored ← instantiateMVars restored
    if restored.hasMVar then
      throwError "printed term left unresolved metavariables:\n{printed}"
    unless ← isDefEq original restored do
      throwError "printed term changed its meaning:\n{printed}"

local syntax "#forth_roundtrip " term " contains " str : command

elab_rules : command
  | `(#forth_roundtrip $term contains $expected:str) =>
      liftTermElabM <| checkRoundTrip term expected.getString

-- The helper checks ordinary Lean output as well as embedded Forth syntax.
#forth_roundtrip ([1, 2, 3] : List Nat) contains "[1, 2, 3]"
#forth_roundtrip ([] : List Int) contains "[]"

-- Finite bodies, every primitive, and negative literals versus subtraction.
#forth_roundtrip [forth|] contains "[forth|]"
#forth_roundtrip [forth| 5 -3 - 3 DUP SWAP DROP + - * =] contains "[forth|"
#forth_roundtrip [forth| IF ELSE THEN] contains "[forth|"
#forth_roundtrip [forth|
    IF 1 IF 2 ELSE 3 THEN ELSE IF 4 ELSE 5 THEN THEN] contains "[forth|"

-- Symbolic pushes retain their Lean binding, including nontrivial expressions.
#forth_roundtrip (fun (a b : Int) => [forth| a b {a + b} +]) contains "[forth|"
#forth_roundtrip (fun (SQUARE : Int) => [forth| SQUARE CALL SQUARE]) contains "CALL SQUARE"
-- This binder is deliberately unused: it must still force CALL on printing.
set_option linter.unusedVariables false in
#forth_roundtrip (fun (SQUARE : Bool) => [forth| CALL SQUARE]) contains "CALL SQUARE"
#forth_roundtrip (fun («DUP» «IF» : Int) =>
    [Instr.push «DUP», Instr.push «IF», Instr.call "DUP", Instr.call "IF"])
    contains "[forth|"
#forth_roundtrip (fun («SUM-OF-SQUARES» : Int) =>
    [Instr.push «SUM-OF-SQUARES», Instr.call "SUM-OF-SQUARES"])
    contains "[forth|"
#forth_roundtrip (fun (a : Int) =>
    (a, fun (a : Int) => [Instr.push a, Instr.call "a", Instr.call "a_1"]))
    contains "[forth|"

private def globalValue : Int := 7
#forth_roundtrip [Instr.push globalValue] contains "{globalValue}"

-- Names use the existing name grammar, with escaping or CALL when necessary.
#forth_roundtrip [forth| SUM-OF-SQUARES] contains "SUM-OF-SQUARES"
#forth_roundtrip [Instr.call "+", Instr.call "IF", Instr.call "CALL", Instr.call "A.B",
    Instr.call "with space", Instr.call "λ"] contains "[forth|"
#forth_roundtrip [Instr.call ""] contains "«»"
#forth_roundtrip [forthDecl| : SQUARE DUP * ;] contains "[forthDecl|"
#forth_roundtrip [forthDecl| : EMPTY ;] contains "[forthDecl|"
#forth_roundtrip [forthProgram|] contains "[forthProgram|]"
#forth_roundtrip [forthProgram|
    : SQUARE DUP * ;
    : SUM-OF-SQUARES SQUARE SWAP SQUARE + ;
    3 4 SUM-OF-SQUARES] contains "[forthProgram|"
#forth_roundtrip (fun (SQUARE : Int) =>
    [forthProgram| : SQUARE DUP * ; SQUARE CALL SQUARE]) contains "[forthProgram|"

-- Unsupported pieces retain ordinary Lean syntax instead of changing meaning.
#forth_roundtrip [Instr.call "unmatched»"] contains "Instr.call"
#forth_roundtrip (fun (tail : Body) => Instr.push 1 :: tail) contains "[forth|"
#forth_roundtrip (fun (name : String) => [Instr.call name]) contains "Instr.call"
#forth_roundtrip (fun (op : Prim) => [Instr.prim op]) contains "Instr.prim"
#forth_roundtrip (fun (op : Prim) => [Instr.push 1, Instr.prim op, Instr.push 2])
    contains "[forth|"
#forth_roundtrip (fun (yes : Body) => [Instr.branch yes []]) contains "Instr.branch"
#forth_roundtrip (fun (name : String) => Decl.mk name []) contains "name"
#forth_roundtrip (fun (decls : List Decl) => Program.mk decls [forth| 1]) contains "decls"

section
-- A displayed constructor prefix must not depend on the local meaning of ++.
local instance : HAppend Body Body Body := ⟨fun _ tail => tail⟩
example (before after : Body) : before ++ after = after := rfl
#forth_roundtrip (fun (tail : Body) => Instr.push 1 :: tail) contains "List.append"
#forth_roundtrip (fun («List.append» : Int) (tail : Body) =>
    Instr.push «List.append» :: tail) contains "List.append"
end

set_option pp.notation false in
#forth_roundtrip [forth| 1 DUP *] contains "List.cons"

set_option pp.explicit true in
#forth_roundtrip [forth| 1 DUP *] contains "List.cons"

set_option pp.miniForth false in
#forth_roundtrip [forth| 1 DUP *] contains "Instr.prim"

/-- info: [forth|] : List Instr -/
#guard_msgs in
#check [forth|]

-- Narrow displays preserve the nesting of conditionals.
/--
info: [forth|
  IF
    1
    IF 2 ELSE 3 THEN
  ELSE
    IF 4 ELSE 5 THEN
  THEN]
-/
#guard_msgs in
run_elab do
  let body ← elabTerm (← `([forth|
    IF 1 IF 2 ELSE 3 THEN ELSE IF 4 ELSE 5 THEN THEN])) none
  synthesizeSyntheticMVarsNoPostponing
  let body ← instantiateMVars body
  logInfo ((← Lean.PrettyPrinter.ppExpr body).pretty 30)

open Deep

-- This is the student's actual view while proving a program equivalence.
/--
trace: env : Env
a b : Int
⊢ Equiv env [forth| a b +] [forth| b a +]
-/
#guard_msgs in
example (env : Env) (a b : Int) :
    Equiv env [forth| a b +] [forth| b a +] := by
  trace_state
  intro s r
  simp [Prim.eval, Int.add_comm]

end MiniForth.PrettyPrinterTests
