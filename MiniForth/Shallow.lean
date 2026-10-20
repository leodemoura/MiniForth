import MiniForth.Basic

/-!
# A shallow embedding: words are Lean functions

The head of a stack is its top. A word either returns a new stack or a runtime
error. Sequencing propagates errors, so equations between words account for
underflow as well as successful executions.

There is no object-language dictionary here: `square` and `cube` are ordinary
Lean definitions, and Lean resolves their names. Higher-order functions and
structural recursion are available directly. The price is that a `Word` has no
syntax tree to inspect or transform. Recursive Lean definitions must also meet
Lean's termination requirements; arbitrary recursive Forth calls do not.
-/

namespace MiniForth.Shallow

abbrev Word := Stack → Result

def skip : Word := fun s => .ok s

def seq (first second : Word) : Word := fun s =>
  match first s with
  | .ok s' => second s'
  | .error e => .error e

scoped infixr:55 " >>> " => seq

def push (value : Int) : Word := fun s => .ok (value :: s)

def prim (op : Prim) : Word := op.eval

def add : Word := prim .add
def sub : Word := prim .sub
def mul : Word := prim .mul
def dup : Word := prim .dup
def swap : Word := prim .swap
def drop : Word := prim .drop
def eq : Word := prim .eq

/-- Consume the flag; zero selects `no` and every other integer selects `yes`. -/
def branch (yes no : Word) : Word
  | [] => .error .stackUnderflow
  | flag :: s => if flag = 0 then no s else yes s

@[simp] theorem skip_seq (w : Word) : skip >>> w = w := rfl

@[simp] theorem seq_skip (w : Word) : w >>> skip = w := by
  funext s
  simp only [seq, skip]
  cases w s <;> rfl

theorem seq_assoc (a b c : Word) : (a >>> b) >>> c = a >>> (b >>> c) := by
  funext s
  simp only [seq]
  cases a s <;> rfl

theorem seq_error (a b : Word) (s : Stack) (e : RuntimeError)
    (h : a s = .error e) : (a >>> b) s = .error e := by
  simp [seq, h]

def square : Word := dup >>> mul

def cube : Word := dup >>> square >>> mul

def sumOfSquares : Word := square >>> swap >>> square >>> add

/-- These proofs apply to every untouched stack suffix, not only an empty one. -/
@[simp] theorem square_run (a : Int) (s : Stack) :
    square (a :: s) = .ok (a * a :: s) := rfl

@[simp] theorem cube_run (a : Int) (s : Stack) :
    cube (a :: s) = .ok (a * (a * a) :: s) := rfl

@[simp] theorem sumOfSquares_run (a b : Int) (s : Stack) :
    sumOfSquares (b :: a :: s) = .ok ((a * a + b * b) :: s) := by
  simp [sumOfSquares, seq, square, swap, add, dup, mul, prim, Prim.eval,
    Int.add_comm]

/-- Function equality includes the empty-stack error case. -/
theorem double_eq : dup >>> add = push 2 >>> mul := by
  funext s
  cases s with
  | nil => rfl
  | cons a s =>
    simp only [seq, dup, add, push, mul, prim, Prim.eval]
    congr 2
    omega

/-- A host-language parameter creates a whole family of words. -/
def offset (amount : Int) : Word := push amount >>> add

@[simp] theorem offset_run (amount a : Int) (s : Stack) :
    offset amount (a :: s) = .ok ((a + amount) :: s) := rfl

/-- Ordinary equational reasoning proves a law for the whole family. -/
theorem offset_seq (a b : Int) : offset a >>> offset b = offset (a + b) := by
  funext s
  cases s <;> simp [offset, seq, push, add, prim, Prim.eval, Int.add_assoc]

/-- Lean accepts this recursion because the natural-number argument decreases. -/
def iterate : Nat → Word → Word
  | 0, _ => skip
  | n + 1, w => w >>> iterate n w

theorem iterate_add (m n : Nat) (w : Word) :
    iterate (m + n) w = iterate m w >>> iterate n w := by
  induction m with
  | zero => simp [iterate]
  | succ m ih => simp [Nat.succ_add, iterate, ih, seq_assoc]

def addN (n : Nat) : Word := iterate n (offset 1)

/-- Induction over a Lean parameter verifies all these generated words at once. -/
theorem addN_run (n : Nat) (a : Int) (s : Stack) :
    addN n (a :: s) = .ok ((a + (n : Int)) :: s) := by
  induction n generalizing a with
  | zero => simp [addN, iterate, skip]
  | succ n ih =>
    change (offset 1 >>> addN n) (a :: s) = _
    simp only [seq, offset_run, ih]
    congr 2
    omega

-- Lean checks these examples by reduction, with no separate evaluator.
example : (push 3 >>> push 4 >>> sumOfSquares) [] = .ok [25] := rfl
example : (push 3 >>> cube) [] = .ok [27] := rfl
example : square [] = .error .stackUnderflow := rfl
example : sumOfSquares [3] = .error .stackUnderflow := rfl
example : addN 5 [10, 99] = .ok [15, 99] := rfl
example : branch (push 7) (push 8) [-2, 99] = .ok [7, 99] := rfl
example : branch (push 7) (push 8) [0, 99] = .ok [8, 99] := rfl

end MiniForth.Shallow
