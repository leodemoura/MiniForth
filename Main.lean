import MiniForth

open MiniForth

private def showRun (label : String) (p : Program) (fuel : Nat := 100) : IO Unit := do
  match p.link with
  | .error e => IO.println s!"{label}: link error {repr e}"
  | .ok env =>
    match Deep.run env fuel p.main with
    | some (.ok s) => IO.println s!"{label}: {repr s}"
    | some (.error e) => IO.println s!"{label}: runtime error {repr e}"
    | none => IO.println s!"{label}: fuel exhausted after {fuel} steps"

/-- Print the same transitions used by the verified evaluator. -/
private def showTrace (env : Env) : Nat → Deep.Config → IO Unit
  | fuel, c => do
    IO.println s!"  {repr c}"
    match fuel, c with
    | n + 1, .run (i :: rest) s => showTrace env n (Deep.transition env i rest s)
    | _, _ => pure ()

def main : IO Unit := do
  IO.println "MiniForth: the top of the stack is on the left."
  IO.println s!"Shallow sum of squares: {repr (Shallow.sumOfSquares [4, 3])}"
  showRun "Deep sum of squares" Examples.arithmetic
  IO.println s!"Shallow conditional addition: {repr (Conditionals.addWhen [-1, 20, 10])}"
  showRun "Deep conditional addition" Conditionals.program
  showRun "False flag without operands"
    { Conditionals.program with main := [forth| 0 ADD-WHEN] }
  showRun "True flag without operands"
    { Conditionals.program with main := [forth| -1 ADD-WHEN] }
  showRun "Recursive factorial of 5" Recursion.factorial
  showRun "Forward reference" [forthProgram|
    : CUBE DUP SQUARE * ;
    : SQUARE DUP * ;
    3 CUBE
  ]
  showRun "Stack underflow" [forthProgram| 3 +]
  showRun "Undefined word" [forthProgram| MISSING]
  showRun "Duplicate declaration" [forthProgram| : X 1 ; : X 2 ; X]
  showRun "Recursive FOREVER" [forthProgram| : FOREVER FOREVER ; FOREVER] 20
  IO.println "Small-step trace of 3 SQUARE:"
  showTrace Examples.arithmetic.env 10 (.run [forth| 3 SQUARE] [])
