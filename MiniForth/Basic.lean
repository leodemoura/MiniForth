import Std

/-!
# The common vocabulary

The head of a list is the top of the stack. Arithmetic uses mathematical integers,
so there is no machine overflow. In `a b -`, `b` is on top and the result is `a - b`.
As in Forth, zero is false and every nonzero integer is true; `=` produces `-1` or `0`.
-/

namespace MiniForth

abbrev Stack := List Int

inductive RuntimeError where
  | stackUnderflow
  | unknownWord (name : String)
  deriving Repr, DecidableEq

abbrev Result := Except RuntimeError Stack

inductive Prim where
  | add | sub | mul | dup | swap | drop | eq
  deriving Repr, DecidableEq

/-- Primitive operations are shared by the two embeddings. -/
def Prim.eval : Prim → Stack → Result
  | .add, b :: a :: s => .ok ((a + b) :: s)
  | .sub, b :: a :: s => .ok ((a - b) :: s)
  | .mul, b :: a :: s => .ok ((a * b) :: s)
  | .dup, a :: s => .ok (a :: a :: s)
  | .swap, b :: a :: s => .ok (a :: b :: s)
  | .drop, _ :: s => .ok s
  | .eq, b :: a :: s => .ok ((if a = b then -1 else 0) :: s)
  | _, _ => .error .stackUnderflow

inductive Instr where
  | push (value : Int)
  | prim (op : Prim)
  | call (name : String)
  | branch (yes no : List Instr)
  deriving Repr, BEq

abbrev Body := List Instr

structure Decl where
  name : String
  body : Body
  deriving Repr, BEq

structure Program where
  decls : List Decl
  main : Body
  deriving Repr, BEq

abbrev Env := String → Option Body

/-- A global dictionary: names are resolved when a word is executed. -/
def Program.env (p : Program) : Env := fun name =>
  (p.decls.find? (fun d => d.name == name)).map Decl.body

def emptyEnv : Env := fun _ => none

end MiniForth
