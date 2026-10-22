import MiniForth.Link
import MiniForth.Equivalence
import MiniForth.WeakestPrecondition

/-!
# Conditional stack requirements

ADD-WHEN consumes a flag. If it is nonzero, add the next two values; otherwise
leave the rest of the stack alone. Thus `[0]` succeeds, but `[-1]` underflows.
Requiring three stack entries on every input would be sufficient, but too strong.

The shallow embedding reuses Lean functions. The deep embedding exposes a conditional in
its syntax, letting us express and verify a rewrite that negates the condition
and swaps the branches.
-/

namespace MiniForth.Conditionals

open Deep

open Shallow
def addWhen : Prog := branch add skip

def body : Body := [forth| IF + ELSE THEN]

def program : Program := [forthProgram|
  : ADD-WHEN IF + ELSE THEN ;
  10 20 -1 ADD-WHEN
]

#eval addWhen [-1, 20, 10]

open Shallow in
#eval run (push 20 >>> push 10 >>> push (-1) >>> addWhen)

#eval runMain program

theorem program_wellFormed : program.WellFormed := by
  simp [Program.WellFormed, Program.calls, Body.calls, program, Program.env]

/-- The flag is consumed even when no addition is requested. -/
theorem addWhen_zero (s : Stack) : addWhen (0 :: s) = .ok s := rfl

/-- Every nonzero integer is true, and the unused suffix is preserved. -/
theorem addWhen_nonzero (h : flag ≠ 0) (a b : Int) (s : Stack) :
    addWhen (flag :: b :: a :: s) = .ok ((a + b) :: s) := by
  simp [addWhen, Shallow.branch, Shallow.add, Shallow.bin, h]

/-- Read a one-instruction conditional derivation in either direction. -/
private theorem exec_branch : Exec env (.branch yes no) s r ↔
    match s with
    | [] => r = .error .stackUnderflow
    | flag :: rest => if flag = 0 then Eval env no rest r else Eval env yes rest r := by
  cases s with
  | nil =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact .branchUnderflow
  | cons flag rest =>
    by_cases h : flag = 0
    · subst flag
      simp only [ite_true]
      constructor
      · intro he
        cases he with
        | branchZero hb => exact hb
        | branchNonzero hn _ => exact False.elim (hn rfl)
      · exact Exec.branchZero
    · simp only [h, ite_false]
      constructor
      · intro he
        cases he with
        | branchZero _ => exact False.elim (h rfl)
        | branchNonzero _ hb => exact hb
      · exact Exec.branchNonzero h

theorem add_eq (s : Stack) : Prim.add.eval s = Shallow.add s := by
  cases s with
  | nil => rfl
  | cons b tail => cases tail <;> rfl


/-- The two embeddings agree on every stack and every outcome, including errors. -/
theorem correspondence : Eval env body s r ↔ addWhen s = r := by
  cases s with
  | nil => simp [body, exec_branch, addWhen, Shallow.branch, eq_comm]
  | cons flag rest =>
    by_cases h : flag = 0 <;>
      simp [body, exec_branch, addWhen, Shallow.branch, Shallow.skip, add_eq, h, eq_comm]

theorem call_correspondence :
    Eval program.env [forth| ADD-WHEN] s r ↔ addWhen s = r :=
  (call_equiv (env := program.env) (name := "ADD-WHEN") (body := body) rfl s r).trans
    correspondence

/-- The exact weakest precondition depends on which branch is selected. -/
theorem wp_exact (Q : Assertion) (s : Stack) : WP env body Q s ↔
    match s with
    | [] => False
    | flag :: rest =>
      if flag = 0 then Q rest
      else ∃ a b tail, rest = b :: a :: tail ∧ Q ((a + b) :: tail) := by
  cases s with
  | nil => simp [body]
  | cons flag rest =>
    by_cases h : flag = 0
    · subst flag
      simp [body]
    · simp only [h, ite_false, body, wp_branch_nonzero h]
      cases rest with
      | nil => simp [wp_prim, Prim.eval]
      | cons b rest => cases rest <;> simp [wp_prim, Prim.eval] <;> grind

/-- Negating the flag and exchanging the branches preserves errors as well as values. -/
theorem flipped_equiv : Equiv env body [forth| 0 = IF ELSE + THEN] := by
  intro s r
  cases s with
  | nil => simp [body, exec_branch, eval_prim, Prim.eval]
  | cons flag rest =>
    by_cases h : flag = 0 <;> simp [body, exec_branch, eval_prim, Prim.eval, h]

-- The false branch can safely run without either addition operand.
example : WP emptyEnv body (fun s => s = []) [0] := by simp [wp_exact]
example : ¬ WP emptyEnv body (fun _ => True) [-1] := by simp [wp_exact]

-- These executions cover missing flags, incomplete operands, both branches,
-- a noncanonical true flag, and an untouched stack suffix.
example : run emptyEnv 2 body [] = some (.error .stackUnderflow) := rfl
example : run emptyEnv 2 body [0] = some (.ok []) := rfl
example : run emptyEnv 2 body [7] = some (.error .stackUnderflow) := rfl
example : run emptyEnv 2 body [-1, 20] = some (.error .stackUnderflow) := rfl
example : run emptyEnv 2 body [-7, 20, 10, 99] = some (.ok [30, 99]) := rfl
example : run emptyEnv 2 body [0, 20, 10, 99] = some (.ok [20, 10, 99]) := rfl
example : run program.env 6 program.main = some (.ok [30]) := rfl

end MiniForth.Conditionals
