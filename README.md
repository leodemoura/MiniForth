# MiniForth

A small Lean development for teaching programming language semantics to experienced
engineers taking their first steps in formal verification. It uses Lean **v4.35.0**
and the standard library, with no external dependencies.

```sh
lake build
lake exe miniforth
```

The build checks the examples and proofs. Start with
[`MiniForth/Examples.lean`](MiniForth/Examples.lean), then read the definitions they
use; there is no need to learn all of Lean before meeting Forth.

## The language

Declarations introduce words; the instructions after the declarations are the main
body. In Lean, this is an ordinary term of type `Program`:

```lean
def arithmetic : Program := [forthProgram|
  : SQUARE DUP * ;
  : CUBE DUP SQUARE * ;
  : SUM-OF-SQUARES SQUARE SWAP SQUARE + ;
  3 4 SUM-OF-SQUARES
]
```

The result is `[25]`. The head of a Lean list is the top of the stack. A word acts
on an existing stack: `SQUARE` sends `x :: rest` to `x * x :: rest`, preserving
the unused part. That statement is more useful than checking a few inputs.

The language has integer literals, `+`, `-`, `*`, `=`, `DUP`, `SWAP`, `DROP`, word
calls, and `IF ... ELSE ... THEN`. Quotation boundaries are explicit:
`[forth| DUP *]` is a body; `[forthDecl| : SQUARE DUP * ;]` is one declaration.
Hyphenated names and negative literals are supported. Names use Lean identifier
segments; use an escaped identifier such as `«SQUARE-2»` when a name contains a
numeric segment or a reserved keyword. MiniForth names are case-sensitive.

Inside a quotation, a name bound to a Lean local variable pushes its value as an
integer; other names call Forth words. Use `{term}` to push a Lean expression,
such as `{a + b}`, and `CALL name` to force a word call when names overlap.
Primitives retain their meaning, and declaration names always name Forth words.
Global Lean definitions require explicit interpolation. These features construct
syntax trees parameterized by Lean values; they do not add runtime variables to
MiniForth.

The semantic choices are deliberate:

- Integers are mathematical integers, not bounded machine words.
- In `3 4 -`, the result is `-1`. The top operand is the right operand.
- Zero is false; every nonzero integer is true. `=` produces `-1` or `0`.
- `IF` consumes its condition. Insufficient operands cause `stackUnderflow`.
- A program has one global dictionary. Forward references and recursion are allowed.
- Linking rejects duplicate declarations and unresolved calls, including calls in
  unselected branches. Linking checks names, not stack safety or termination.
- `LinkCorrectness.lean` proves that successful linking prevents unknown-word
  runtime errors on every input stack.
- Direct evaluation of an unlinked body can report `unknownWord`. The semantics
  remains defined on malformed programs, which lets us state what validation buys us.
- Exhausted fuel means “execution has not finished within this budget.” It is
  neither a runtime error nor a proof of divergence.

This is a teaching language inspired by Forth, not an implementation of a Forth
standard. In particular, its global dictionary does not model an interactive
dictionary with successive redefinitions.

## Suggested course sequence

1. **Functions and contracts.** Trace the arithmetic example by hand. Introduce
   stacks, `Except`, pattern matching, and the difference between a computed example
   and a theorem quantified over every input and every unused stack suffix.
2. **Shallow embedding.** Read `MiniForth/Shallow.lean`. A word is a Lean function;
   composition propagates errors. Prove `square_run` and use ordinary function
   equality to express equivalence. Explore the family of words built with `iterate`.
3. **Deep embedding and syntax.** Read `Basic.lean`, `Syntax.lean`, and `Link.lean`.
   The same word is now data. Inspect the AST and separate parsing, name checking,
   and execution. Explain that quotation is convenient notation, not a new semantics.
4. **Big-step and small-step semantics.** Read `Deep.lean`. Big-step derivations
   describe completed computations; small steps expose each transition. Follow a
   call and a branch, then a recursive word. Connect the relations to the executable
   evaluator and explain why a fuel limit does not define the language's meaning.
   `Recursion.lean` proves factorial correct for every natural input;
   `Divergence.lean` proves that `FOREVER` never produces any result.
5. **Program equivalence.** Start with `ProgramEquivalence.lean`: prove familiar
   algebraic laws between quoted programs. Then read `Equivalence.lean`, prove a
   local optimization, and lift it through sequencing. Compare `SWAP SWAP` with
   the empty body, including short input stacks. Discuss why a correct optimizer
   must preserve failures.
6. **Weakest preconditions.** Read `WeakestPrecondition.lean` and the worked
   contracts in `Examples.lean`. Calculate backwards through a sequence. Separate
   successful termination (total correctness), partial correctness, and safety.
   Then read `Conditionals.lean`: its exact precondition shows how the required
   stack depth can depend on which branch is selected.

The order intentionally introduces declarations before recursion. The initial
arithmetic examples need no recursive definitions; branching and recursion are
available when the class is ready for them.

The longer infrastructure proofs in `Deep.lean` and `LinkCorrectness.lean` can be
an optional second pass. The first lessons only need to read their statements
and work with the smaller program proofs in `Shallow.lean` and `Examples.lean`.

## What each embedding makes easy—and what it costs

| Question | Shallow embedding | Deep embedding |
| --- | --- | --- |
| What is a word? | A Lean function `Stack → Result` | An instruction list interpreted in a dictionary |
| Who resolves a call? | Lean resolves an identifier | The language resolves a string in `Env` |
| How do we build word families? | Ordinary higher-order functions and natural-number recursion | Functions that generate syntax |
| How do we prove arithmetic behavior? | Unfold functions, simplify, reason about integers | Invert or construct semantic derivations, then reason about integers |
| How do we inspect or transform a program? | No object-language AST is provided by this representation | Pattern match on constructors and prove the transformation correct |
| How do we show execution progress? | Function application gives a result | Small-step configurations expose remaining code and the stack |
| What about recursion? | A Lean definition must meet Lean's termination requirements | The syntax admits recursion; a semantic derivation describes a finite execution |
| What infrastructure is required? | A small library of stack functions | Syntax, name validation, semantic relations, an evaluator, and connecting proofs |

The examples make these differences observable:

- `square`, `cube`, and `sumOfSquares` reuse ordinary Lean definitions in the shallow
  embedding. There is no string lookup or separate linker.
- A shallow `iterate n word` demonstrates host-language abstraction. The host can
  supply features beyond the MiniForth grammar, so decide which features a model
  intends to expose before treating every shallow term as a MiniForth program.
- The deep arithmetic program uses Forth declarations and calls. Changing a call
  to an undeclared name produces a link error; a shallow misspelling is a Lean
  elaboration error. Forward references do not depend on declaration order.
- Constant folding examines deep syntax and comes with a theorem about behavior.
  An AST enables this proof; it does not make the proof automatic.
- A deep recursive word can run forever. A finite run with no result is only an
  observation about that run. A divergent Lean function cannot simply be admitted
  as an ordinary total shallow word.

The executable prints both arithmetic results, conditional addition, factorial,
validation errors, underflow, an exhausted run, and a small-step trace of `3 SQUARE`.

These are tradeoffs of the chosen representations, not claims that shallow
embeddings can never have custom notation or model divergence. For example, a
different shallow embedding could use relations or explicit partial computations.

## A conditional example

[`Conditionals.lean`](MiniForth/Conditionals.lean) pairs these definitions:

```lean
def addWhen : Shallow.Word := Shallow.branch Shallow.add Shallow.skip

def program : Program := [forthProgram|
  : ADD-WHEN IF + ELSE THEN ;
  10 20 -1 ADD-WHEN
]
```

Both produce `[30]`. `ADD-WHEN` consumes its flag. With zero it leaves the rest
of the stack alone; with any nonzero integer it adds the next two values.
Consequently `[0]` succeeds with `[]`, while `[-1]` causes underflow.

The correspondence theorem covers every stack and every outcome. The exact WP
requires a flag, then either a zero flag with the postcondition already true of
the remaining stack, or a nonzero flag with two operands whose sum establishes
the postcondition. Requiring three entries on every input would exclude valid
calls with a zero flag.

The shallow version reuses ordinary functions; the deep version exposes a branch
as syntax. The example also proves that `IF + ELSE THEN` is equivalent to
`0 = IF ELSE + THEN`: negating the condition and exchanging the branches
preserves successes and errors, including for nonzero flags other than `-1`.

## Program equivalence examples

[`ProgramEquivalence.lean`](MiniForth/ProgramEquivalence.lean) contains proofs in
the notation used to write the programs themselves:

```lean
open MiniForth MiniForth.Deep

example (env : Env) (a b : Int) :
    Equiv env [forth| a b +] [forth| b a +] := by
  intro s r
  simp [Prim.eval, Int.add_comm]
```

Here `a` and `b` are arbitrary Lean integers inserted as literal-push instructions.
Introducing `s` and `r` asks Lean to compare the two programs on every initial
stack and every outcome. Simplifying execution reduces the proof to an integer law.

The file also proves multiplication commutativity, addition associativity,
distributivity, duplication and push/drop rewrites, and combining two offsets:
`a + b +` is equivalent to `{a + b} +`, including on the empty input stack.
Another theorem reuses addition commutativity inside arbitrary surrounding code.
The counterexample `0 +` versus an empty body shows where an arithmetic identity
alone is insufficient: the addition can underflow.

## Contracts and equivalence

Equivalence compares all completed outcomes, including runtime errors, for every
initial stack. Thus it does not identify a failing computation with one that runs
forever. It deliberately ignores execution cost and intermediate configurations.

`WP env code Q s` means that `code` successfully terminates from `s` and its result
satisfies `Q`. The sequencing rule is:

```text
WP (a ++ b) Q = WP a (WP b Q)
```

This is a logical characterization; recursive programs do not acquire a terminating
WP calculation algorithm for free. `WLP` constrains successful outcomes only, so
it permits both failures and divergence. `SafeWLP` additionally rules out runtime
errors while still allowing divergence. The distinction is explicit rather than
hidden in a convention about what “correct” means.

`Hoare` is defined using this total-correctness contract, so `wp_weakest` simply
unpacks its definition. The sequencing theorem and primitive rules justify
calculating preconditions backwards; determinism justifies the theorem that
total correctness implies safe partial correctness.

## Exercises

- Add `OVER` to both embeddings and prove that it preserves the unused stack.
- Derive the exact weakest precondition of `SWAP +` for a chosen postcondition.
- State the stack-length precondition under which `SWAP SWAP` is an identity.
- Prove a new constant-folding rule for subtraction, checking operand order.
- Extend the optimizer to nested branches and state its preservation theorem.
- Adapt the factorial proof to a tail-recursive implementation. Prove what happens
  on negative input, which is outside the existing natural-number contract.
- Replace mathematical integers with bounded words and revisit the arithmetic proofs.
