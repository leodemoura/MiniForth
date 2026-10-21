import MiniForth.Quotation

/-!
# MiniForth in proof goals

Delaboration recovers the embedded notation from the actual syntax tree. It does
not evaluate programs or unfold definitions. Complete constructor lists become
quotations, and a known prefix of an open body is displayed using
`List.append [forth| ...] rest`. Symbolic instructions and symbolic word names keep Lean's
ordinary representation.

`set_option pp.miniForth false` exposes the constructors again. Lean's general
`pp.notation` option also controls this notation.
-/

open Lean PrettyPrinter Delaborator SubExpr

namespace MiniForth.PrettyPrinter

private def enabled : DelabM Unit := do
  guard (← getPPOption pp.miniForth.get)
  guard (← getPPOption getPPNotation)
  guard (!(← getPPOption getPPExplicit))

/-- Parse only a word name, checking that escaping preserves the string value.
Strings that cannot be written in the name grammar use ordinary Lean syntax. -/
private def delabName : DelabM (TSyntax `forthName) := do
  let .lit (.strVal name) ← getExpr | failure
  for spelling in [name, "«" ++ name ++ "»"] do
    if let .ok stx := Parser.runParserCategory (← getEnv) `forthName spelling then
      let stx : TSyntax `forthName := ⟨stx⟩
      if forthNameString stx == name then
        -- The temporary parser input is not a location in the user's source.
        return ⟨stx.raw.rewriteBottomUp (·.setInfo .none)⟩
  failure

/-- Attach each embedded instruction to its original expression in the InfoView. -/
private def annotate {kind : SyntaxNodeKind} (stx : TSyntax kind) : DelabM (TSyntax kind) := do
  let annotated ← annotateTermInfo ⟨stx.raw⟩
  return ⟨annotated.raw⟩

/-- A traversal of constructor lists which preserves subexpression positions. -/
private partial def delabList {kind : SyntaxNodeKind} (type : Name)
    (element : DelabM (TSyntax kind)) : DelabM (Array (TSyntax kind)) := do
  let e ← getExpr
  if e.isMData then
    return ← withMDataExpr (delabList type element)
  if e.isAppOfArity ``List.nil 1 then
    guard (e.getArg! 0 |>.isConstOf type)
    return #[]
  guard (e.isAppOfArity ``List.cons 3)
  guard (e.getArg! 0 |>.isConstOf type)
  let head ← withNaryArg 1 element
  let tail ← withNaryArg 2 (delabList type element)
  return #[head] ++ tail

private def delabPush : DelabM (TSyntax `forthInstr) := do
  let value ← delab
  match value with
  | `($n:num) => `(forthInstr| $n:num)
  | `(- $n:num) => `(forthInstr| -$n:num)
  | _ =>
    -- Only local identifiers can be written bare: a global Lean identifier
    -- would instead become a call to a Forth word.
    if (← getExpr).isFVar && value.raw.isIdent then
      let id : Ident := ⟨value.raw⟩
      if let .ok parsed := Parser.runParserCategory (← getEnv) `forthInstr
          (id.getId.toString) then
        if let `(forthInstr| $name:forthName) := parsed then
          if name.raw[1].getArgs.isEmpty && name.raw[0].getId == id.getId then
            let name ← `(forthName| $id:ident)
            return ← `(forthInstr| $name:forthName)
    `(forthInstr| {$value})

private def delabPrim : DelabM (TSyntax `forthInstr) := do
  match (← getExpr).constName? with
  | some ``Prim.add => `(forthInstr| +)
  | some ``Prim.sub => `(forthInstr| -)
  | some ``Prim.mul => `(forthInstr| *)
  | some ``Prim.dup => `(forthInstr| DUP)
  | some ``Prim.swap => `(forthInstr| SWAP)
  | some ``Prim.drop => `(forthInstr| DROP)
  | some ``Prim.eq => `(forthInstr| =)
  | _ => failure

private def delabCall : DelabM (TSyntax `forthInstr) := do
  let name ← delabName
  let mut collides := false
  if name.raw[1].getArgs.isEmpty then
    let id := name.raw[0].getId
    for localDecl in ← getLCtx do
      if localDecl.userName == id then
        collides := true
  if collides then
    `(forthInstr| CALL $name)
  else
    `(forthInstr| $name:forthName)

private partial def delabInstr : DelabM (TSyntax `forthInstr) := do
  let e ← getExpr
  if e.isMData then
    return ← withMDataExpr delabInstr
  let stx ←
    if e.isAppOfArity ``Instr.push 1 then
      withNaryArg 0 delabPush
    else if e.isAppOfArity ``Instr.prim 1 then
      withNaryArg 0 delabPrim
    else if e.isAppOfArity ``Instr.call 1 then
      withNaryArg 0 delabCall
    else if e.isAppOfArity ``Instr.branch 2 then do
      let yes ← withNaryArg 0 (delabList ``Instr delabInstr)
      let no ← withNaryArg 1 (delabList ``Instr delabInstr)
      `(forthInstr| IF $yes* ELSE $no* THEN)
    else
      failure
  annotate stx

private def delabDecl : DelabM (TSyntax `forthDecl) := do
  guard ((← getExpr).isAppOfArity ``Decl.mk 2)
  let name ← withNaryArg 0 delabName
  let body ← withNaryArg 1 (delabList ``Instr delabInstr)
  annotate (← `(forthDecl| : $name $body* ;))

/-- A known prefix of an open body can still use Forth notation. The tail keeps
its ordinary representation, so a continuation variable remains visible. -/
private partial def delabBodyParts :
    DelabM (Array (TSyntax `forthInstr) × Option Term) := do
  let e ← getExpr
  if e.isMData then
    return ← withMDataExpr delabBodyParts
  if e.isAppOfArity ``List.nil 1 then
    guard (e.getArg! 0 |>.isConstOf ``Instr)
    return (#[], none)
  guard (e.isAppOfArity ``List.cons 3)
  guard (e.getArg! 0 |>.isConstOf ``Instr)
  let head ← withNaryArg 1 delabInstr
  let (tail, rest) ← withNaryArg 2 <|
    delabBodyParts <|> do pure (#[], some (← delab))
  return (#[head] ++ tail, rest)

@[app_delab List.nil, app_delab List.cons]
def delabBody : Delab := do
  enabled
  let (body, rest) ← delabBodyParts
  let quoted ← `([forth| $body*])
  if let some rest := rest then do
    -- Introducing overloaded `++` could select a different local HAppend
    -- instance. Name the actual list operation, avoiding local name collisions.
    let some appendName ← unresolveNameGlobalAvoidingLocals? ``List.append
        (fullNames := ← getPPOption getPPFullNames) | failure
    let append := mkIdent appendName
    `($append $quoted $rest)
  else
    pure quoted

@[app_delab Decl.mk]
def delabDeclaration : Delab := do
  enabled
  let decl ← delabDecl
  `([forthDecl| $decl])

@[app_delab Program.mk]
def delabProgram : Delab := do
  enabled
  guard ((← getExpr).isAppOfArity ``Program.mk 2)
  let decls ← withNaryArg 0 (delabList ``Decl delabDecl)
  let main ← withNaryArg 1 (delabList ``Instr delabInstr)
  `([forthProgram| $decls:forthDecl* $main:forthInstr*])

end MiniForth.PrettyPrinter
