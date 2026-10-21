import MiniForth.Basic

/-!
# A shallow embedding: Forth programs are Lean functions

```forth
: SQUARE DUP * ;
: CUBE DUP SQUARE * ;
: SUM-OF-SQUARES SQUARE SWAP SQUARE + ;
3 4 SUM-OF-SQUARES
```

A Forth programs takes a stack and either returns a new stack or a runtime
error. Sequencing propagates errors.

There is no object-language dictionary here: `square` and `cube` are ordinary
Lean definitions, and Lean resolves their names. Higher-order functions and
structural recursion are available directly. The price is that a `Prog` has **no**
syntax tree to **inspect** or **transform**.
-/

namespace MiniForth.Shallow

abbrev Prog := Stack → Result

def skip : Prog := fun s => .ok s

def seq (p₁ p₂ : Prog) : Prog := fun s =>
  match p₁ s with
  | .ok s'   => p₂ s'
  | .error e => .error e

scoped infixr:55 " >>> " => seq

def push (value : Int) : Prog :=
  fun s => .ok (value :: s)

def bin (op : Int → Int → Int) : Prog :=
  fun s => match s with
    | b :: a :: s' => .ok (op a b :: s')
    | _ => .error .stackUnderflow

def add := bin (· + ·)
def sub := bin (· - ·)
def mul := bin (· * .)
def eq  := bin fun a b => if a = b then -1 else 0

def drop : Prog :=
  fun s => match s with
    | _ :: s' => .ok s'
    | _ => .error .stackUnderflow

def dup : Prog :=
  fun s => match s with
    | a :: s' => .ok (a :: a :: s')
    | _ => .error .stackUnderflow

def swap : Prog :=
  fun s => match s with
    | a :: b :: s' => .ok (b :: a :: s')
    | _ => .error .stackUnderflow

/-- Consume the flag; zero selects `no` and every other integer selects `yes`. -/
def branch (yes no : Prog) : Prog
  | [] => .error .stackUnderflow
  | flag :: s => if flag = 0 then no s else yes s

@[simp] theorem skip_seq (w : Prog) : skip >>> w = w := rfl

@[simp] theorem seq_skip (w : Prog) : w >>> skip = w := by
  funext s
  simp only [seq, skip]
  cases w s <;> rfl

theorem seq_assoc (a b c : Prog) : (a >>> b) >>> c = a >>> (b >>> c) := by
  funext s
  simp only [seq]
  cases a s <;> rfl

theorem seq_error (a b : Prog) (s : Stack) (e : RuntimeError)
    (h : a s = .error e) : (a >>> b) s = .error e := by
  simp [seq, h]

def square : Prog := dup >>> mul

#eval square [2]

example : square [2] = .ok [4] := by cbv

def cube : Prog := dup >>> square >>> mul

example : cube [2] = .ok [8] := by cbv

example : cube [] = .error .stackUnderflow := by cbv

def sumOfSquares : Prog := square >>> swap >>> square >>> add

example : sumOfSquares [3, 4] = .ok [9+16] := by cbv

def run (p : Prog) := p []

/-
3 4 SUM-OF-SQUARES
-/

#eval run (push 3 >>> push 4 >>> sumOfSquares)

example : run (push 3 >>> push 4 >>> sumOfSquares) = .ok [25] := by cbv

/-- These proofs apply to every untouched stack suffix, not only an empty one. -/
@[simp] theorem square_run (a : Int) (s : Stack) :
    square (a :: s) = .ok (a * a :: s) := rfl

@[simp] theorem cube_run (a : Int) (s : Stack) :
    cube (a :: s) = .ok (a * (a * a) :: s) := rfl

@[simp] theorem sumOfSquares_run (a b : Int) (s : Stack) :
    sumOfSquares (b :: a :: s) = .ok ((a * a + b * b) :: s) := by
  simp [sumOfSquares, seq, swap, add, bin, Int.add_comm]

/-- Function equality includes the empty-stack error case. -/
theorem double_eq : dup >>> add = push 2 >>> mul := by
  funext s
  cases s with
  | nil => rfl
  | cons a s =>
    simp only [seq, dup, add, push, mul, bin]
    congr 2
    omega

/-- A host-language parameter creates a whole family of words. -/
def offset (amount : Int) : Prog := push amount >>> add

@[simp] theorem offset_run (amount a : Int) (s : Stack) :
    offset amount (a :: s) = .ok ((a + amount) :: s) := rfl

/-- Ordinary equational reasoning proves a law for the whole family. -/
theorem offset_seq (a b : Int) : offset a >>> offset b = offset (a + b) := by
  funext s
  cases s <;> simp [offset, seq, push, add, bin, Int.add_assoc]

/-- Lean accepts this recursion because the natural-number argument decreases. -/
def iterate : Nat → Prog → Prog
  | 0, _ => skip
  | n + 1, w => w >>> iterate n w

theorem iterate_add (m n : Nat) (w : Prog) :
    iterate (m + n) w = iterate m w >>> iterate n w := by
  induction m with
  | zero => simp [iterate]
  | succ m ih => simp [Nat.succ_add, iterate, ih, seq_assoc]

def addN (n : Nat) : Prog := iterate n (offset 1)

/-- Induction over a Lean parameter verifies all these generated words at once. -/
theorem addN_run (n : Nat) (a : Int) (s : Stack) :
    addN n (a :: s) = .ok ((a + n) :: s) := by
  induction n generalizing a with
  | zero => simp [addN, iterate, skip]
  | succ n ih =>
    change (offset 1 >>> addN n) (a :: s) = _
    simp only [seq, offset_run, ih]
    congr 2
    lia

-- Lean checks these examples by reduction, with no separate evaluator.
example : (push 3 >>> push 4 >>> sumOfSquares) [] = .ok [25] := by cbv
example : (push 3 >>> cube) [] = .ok [27] := by cbv
example : square [] = .error .stackUnderflow := by cbv
example : sumOfSquares [3] = .error .stackUnderflow := by cbv
example : addN 5 [10, 99] = .ok [15, 99] := by cbv
example : branch (push 7) (push 8) [-2, 99] = .ok [7, 99] := by cbv
example : branch (push 7) (push 8) [0, 99] = .ok [8, 99] := by cbv

end MiniForth.Shallow
