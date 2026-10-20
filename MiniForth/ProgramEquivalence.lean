import MiniForth.Syntax
import MiniForth.Equivalence

/-!
# Algebraic laws for MiniForth programs

The Lean integers `a`, `b`, and `c` become pushed values in these quotations.
They describe a family of concrete programs: no variable lookup is added to
MiniForth. A Lean expression in braces can also supply a pushed value.

`Equiv env p q` compares both programs on every initial stack and every result,
including runtime errors. The first proofs introduce that stack and result,
then simplify the semantics to familiar integer identities.
-/

namespace MiniForth.ProgramEquivalence

open Deep

/-- Changing the order of two pushed integers preserves their sum. -/
theorem add_comm (env : Env) (a b : Int) :
    Equiv env [forth| a b +] [forth| b a +] := by
  intro s r
  simp [Prim.eval, Int.add_comm]

theorem mul_comm (env : Env) (a b : Int) :
    Equiv env [forth| a b *] [forth| b a *] := by
  intro s r
  simp [Prim.eval, Int.mul_comm]

/-- The postfix order records which addition is performed first. -/
theorem add_assoc (env : Env) (a b c : Int) :
    Equiv env [forth| a b + c +] [forth| a b c + +] := by
  intro s r
  simp [Prim.eval, Int.add_assoc]

/-- Distributing multiplication changes the number of instructions. -/
theorem mul_add (env : Env) (a b c : Int) :
    Equiv env [forth| a b c + *] [forth| a b * a c * +] := by
  intro s r
  simp [Prim.eval, Int.mul_add]

/-- DUP can be replaced by another push when the top value is known. -/
theorem dup_expand (env : Env) (a : Int) :
    Equiv env [forth| a DUP *] [forth| a a *] := by
  intro s r
  simp [Prim.eval]

/-- A value introduced and immediately discarded needs no stack precondition. -/
theorem push_drop (env : Env) (a : Int) :
    Equiv env [forth| a DROP] [forth|] := by
  intro s r
  simp [Prim.eval]

/-- Combining offsets also preserves underflow on an empty initial stack. -/
theorem add_offsets (env : Env) (a b : Int) :
    Equiv env [forth| a + b +] [forth| {a + b} +] := by
  intro s r
  cases s <;> simp [Prim.eval, Int.add_assoc]

/-- A local equivalence can be reused inside arbitrary surrounding code. -/
theorem add_comm_in_context (env : Env) (a b : Int) (before after : Body) :
    Equiv env (before ++ [forth| a b +] ++ after)
      (before ++ [forth| b a +] ++ after) := by
  exact ((Equiv.refl before).append (add_comm env a b)).append (Equiv.refl after)

/-- An arithmetic identity is not enough when one program can underflow. -/
theorem zero_add_not_equiv_nil (env : Env) :
    ¬ Equiv env [forth| 0 +] [forth|] := by
  intro h
  have he := (h [] (.ok [])).mpr Eval.nil
  simp [Prim.eval] at he

end MiniForth.ProgramEquivalence
