import MiniForth.Shallow
import MiniForth.Grind.Rules

/-!
# Automating equations in the shallow embedding

These are the same words as in `MiniForth.Shallow`. We register their defining
equations, then ask `grind` to connect execution with integer arithmetic.
`grind` uses function extensionality to compare words on arbitrary stacks.
Induction remains an explicit choice; automation handles the resulting equations.
-/

namespace MiniForth.Grind.Shallow

open MiniForth.Shallow

-- Unfolding exposes function applications and the matches that propagate errors.
-- These registrations are local: importing this lesson does not affect other proofs.
attribute [local grind unfold] skip seq push add
  mul dup swap branch

@[grind =] theorem skip_seq (w : Prog) : skip >>> w = w := by
  grind

@[grind =] theorem seq_skip (w : Prog) : w >>> skip = w := by
  grind

@[grind =] theorem seq_assoc (a b c : Prog) : (a >>> b) >>> c = a >>> (b >>> c) := by
  grind

theorem seq_error (a b : Prog) (s : Stack) (e : RuntimeError)
    (h : a s = .error e) : (a >>> b) s = .error e := by
  grind

attribute [local grind unfold] MiniForth.Shallow.square MiniForth.Shallow.cube
  MiniForth.Shallow.sumOfSquares

theorem square_run (a : Int) (s : Stack) :
    square (a :: s) = .ok (a * a :: s) := by
  grind

theorem cube_run (a : Int) (s : Stack) :
    cube (a :: s) = .ok (a * (a * a) :: s) := by
  grind

theorem sumOfSquares_run (a b : Int) (s : Stack) :
    sumOfSquares (b :: a :: s) = .ok ((a * a + b * b) :: s) := by
  grind

/-- Extensionality and case analysis cover success and underflow automatically. -/
theorem double_eq : dup >>> add = push 2 >>> mul := by
  grind

attribute [local grind unfold] MiniForth.Shallow.offset

theorem offset_run (amount a : Int) (s : Stack) :
    offset amount (a :: s) = .ok ((a + amount) :: s) := by
  grind

theorem offset_seq (a b : Int) : offset a >>> offset b = offset (a + b) := by
  funext s
  cases s <;> grind

-- Normalize a known zero/successor before search; a symbolic count stays opaque.
attribute [local grind norm] iterate.eq_1 iterate.eq_2

/-- Automation uses the induction hypothesis; it does not choose induction. -/
theorem iterate_add (m n : Nat) (w : Prog) :
    iterate (m + n) w = iterate m w >>> iterate n w := by
  induction m <;> grind

attribute [local grind unfold] addN

theorem addN_run (n : Nat) (a : Int) (s : Stack) :
    addN n (a :: s) = .ok ((a + (n : Int)) :: s) := by
  induction n generalizing a <;> grind

example : (push 3 >>> push 4 >>> sumOfSquares) [] = .ok [25] := by grind
example : (push 3 >>> cube) [] = .ok [27] := by grind
example : square [] = .error .stackUnderflow := by grind
example : sumOfSquares [3] = .error .stackUnderflow := by grind
example : addN 5 [10, 99] = .ok [15, 99] := by grind [addN_run]
example : branch (push 7) (push 8) [-2, 99] = .ok [7, 99] := by grind
example : branch (push 7) (push 8) [0, 99] = .ok [8, 99] := by grind

-- A shallow word is itself a function. Track partial applications of `iterate`
-- so an equality between words also gives equality when applied to a stack.
attribute [local grind funCC] iterate

/-- Use a function-valued summary without unfolding either word's implementation. -/
theorem iterate_summary (n : Nat) (w summary : Prog) (s : Stack)
    (h : iterate n w = summary) : iterate n w s = summary s := by
  grind

end MiniForth.Grind.Shallow
