# MiniForth

A small Lean tutorial for programming language semantics.

```sh
lake build
lake exe miniforth
```

The build checks the examples and proofs. Start with
[`MiniForth/Examples.lean`](MiniForth/Examples.lean), then read the definitions they
use; there is no need to learn all of Lean before meeting Forth.

## The language

Declarations introduce new Forth programs; the instructions after the declarations are the main
body. In Lean, this is an ordinary term of type `Program`:

```lean
def arithmetic : Program := [forthProgram|
  : SQUARE DUP * ;
  : CUBE DUP SQUARE * ;
  : SUM-OF-SQUARES SQUARE SWAP SQUARE + ;
  3 4 SUM-OF-SQUARES
]
```

The result is `[25]`. The head of a Lean list is the top of the stack. A Forth program acts
on an existing stack: `SQUARE` sends `x :: rest` to `x * x :: rest`, preserving
the unused part. 

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

Importing `MiniForth.Syntax` also makes goals and messages display these
quotations. For example, an equivalence goal reads:

```text
⊢ Equiv env [forth| a b +] [forth| b a +]
```

The printer handles bodies, declarations, whole programs, and nested conditionals.
Long quotations wrap and indent to fit Lean's `pp.width`. Symbolic values keep
their Lean bindings; calls use `CALL` or escaped names when needed. A known
prefix with an unknown continuation prints as `List.append [forth| SQUARE] rest`.
Using explicit list append preserves its meaning even with a custom `++` instance.
Symbolic instructions or names that the quotation grammar cannot express retain
ordinary Lean syntax. Named definitions remain named.

Use `set_option pp.miniForth false` to inspect the underlying syntax trees during
the course. The general options `pp.notation false` and `pp.explicit true` also
disable Forth notation. The implementation separates parsing and elaboration in
[`Quotation.lean`](MiniForth/Quotation.lean) from goal display in
[`PrettyPrinter.lean`](MiniForth/PrettyPrinter.lean). The
[printer tests](MiniForth/PrettyPrinterTests.lean) check that printed text parses
and elaborates back to the same expression, including at narrow widths.

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
3. **Deep embedding and syntax.** Read `Basic.lean`, `Quotation.lean`, and `Link.lean`.
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
6. **Connecting the embeddings.** Read [`Denote.lean`](MiniForth/Denote.lean).
   Translate deeply embedded Forth programs into shallow functions using `denote`.
   Supply the meanings of calls through `prog`, prove correspondence under
   `CallsAgree`, and transfer shallow function equalities to deep program equivalences.
7. **Weakest preconditions.** Read `WeakestPrecondition.lean` and the worked
   contracts in `Examples.lean`. Calculate backwards through a sequence. Separate
   successful termination (total correctness), partial correctness, and safety.
   Then read `Conditionals.lean`: its exact precondition shows how the required
   stack depth can depend on which branch is selected.
8. **Automation.** Compare the original proofs with the corresponding files in
   `MiniForth/Grind/`. Study which semantic rules are registered, then let `grind`
   handle routine reasoning. Keep induction, useful contracts, and recursive-call
   unfolding visible as choices made by the engineer.

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

[`Denote.lean`](MiniForth/Denote.lean) connects the two representations.
`denote prog code` translates a deeply embedded Forth program into a `Shallow.Prog`.
It maps primitives to their independent shallow implementations, sequences to
composition, and conditionals to `Shallow.branch`. The supplied
`prog : String → Shallow.Prog` gives the meanings of named Forth programs.

`denote_append` proves that concatenation becomes composition. Under
`CallsAgree env prog`, `denote_correct` relates the resulting function to big-step
evaluation, including errors, and `equiv_iff_denote_eq` relates deep equivalence to
function equality. The examples translate `SQUARE`, `CUBE`, and a conditional,
then reuse `Shallow.double_eq` to prove `DUP +` equivalent to `2 *`.
The call agreement assumption requires every call to return a result on every
stack; it cannot hold for a deep environment with a divergent call.

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

## A second pass with `grind`

The original lessons remain unchanged. The files in
[`MiniForth/Grind/`](MiniForth/Grind) give parallel proofs using a shared set of
annotations in [`Rules.lean`](MiniForth/Grind/Rules.lean). For example:

```lean
import MiniForth.Syntax
import MiniForth.Grind.Rules

open MiniForth MiniForth.Deep

example (env : Env) (a b : Int) :
    Equiv env [forth| a b +] [forth| b a +] := by
  grind
```

| Original lesson | Automated version |
| --- | --- |
| Shallow functions and algebra | [`Grind/Shallow.lean`](MiniForth/Grind/Shallow.lean) |
| Program equivalence | [`Grind/ProgramEquivalence.lean`](MiniForth/Grind/ProgramEquivalence.lean) |
| Arithmetic contracts and constant folding | [`Grind/Examples.lean`](MiniForth/Grind/Examples.lean) |
| Weakest preconditions | [`Grind/WeakestPrecondition.lean`](MiniForth/Grind/WeakestPrecondition.lean) |
| Conditional stack requirements | [`Grind/Conditionals.lean`](MiniForth/Grind/Conditionals.lean) |
| Terminating recursion | [`Grind/Recursion.lean`](MiniForth/Grind/Recursion.lean) |
| Divergence | [`Grind/Divergence.lean`](MiniForth/Grind/Divergence.lean) |

The shared annotations expose generic semantic facts. Each lesson then proves its
own contracts and can register them locally for subsequent proofs. For example,
`square_step` describes a call to `SQUARE` with an arbitrary continuation;
`cube_step` uses that contract. The equivalence of `a CUBE` and `a SQUARE a *`
then follows with `by grind`, without expanding either dictionary entry again.

`grind` combines these facts with equality reasoning, case analysis, and integer
arithmetic. The program-equivalence file derives commutativity, associativity,
distributivity, and stack rewrites directly. The conditional lesson also proves:

```lean
example : Equiv env [forth| DUP IF 1 + ELSE DROP 1 THEN] [forth| 1 +] := by
  grind
```

Here the zero-branch condition explains why replacing the top value with `1`
agrees with incrementing it. The proof also covers empty-stack underflow.

The examples use several parts of the automation interface deliberately:

| Feature | Purpose in MiniForth |
| --- | --- |
| `[grind norm]` | Normalize primitive operations and known recursive equations before theorem search. |
| `[grind =]` | Apply a semantic equation or word contract when its left-hand side appears. |
| `[grind unfold]` | Expose selected shallow definitions and the meaning of equivalence. |
| `grind_pattern` with `=?=` | Decompose an instruction sequence specifically when it starts with a call. |
| A multi-pattern with `guard` | Use a successful instruction's output only after its contract is known true and the enclosing instruction sequence appears. |
| `[grind funCC]` | Reuse equality between function-valued shallow words at a particular input stack. |
| `grind only => use ...` | Choose theorem instantiations explicitly in the divergence proof. |

The shallow equations also demonstrate automatic function extensionality.
`grind -funext` in the offset proofs disables speculative splits between function
terms; the ordinary extensionality rule remains available.

The shape of a rule matters. For primitive weakest preconditions, the automation
interface computes the intermediate stack from the primitive result. This avoids
asking proof search to discover that stack as an existential witness. The rule
is proved from the original WP semantics.

Induction is still explicit for iteration, factorial, divergence, and the constant
folder. [`Tactics.lean`](MiniForth/Grind/Tactics.lean) defines `forth_unfold lookup`
as a short macro over `rw` and `simp only`: it expands one call using a dictionary
lookup proof and normalizes list append. The factorial proof is now:

```lean
  induction n generalizing s with
  | zero =>
    forth_unfold factorial_lookup
    grind
  | succ n ih =>
    forth_unfold factorial_lookup
    have recursive := ih ((n + 1 : Int) :: s)
    grind
```

The chosen induction instance preserves the operand needed after the recursive
call; the guarded sequencing rule connects its result to the continuation.
Recursive dictionaries never unfold automatically. These examples use ordinary
tactic limits.

The divergence proof illustrates interactive automation: `use [→ run_complete]`
derives a fuel witness from an assumed finite derivation, `cases_next` extracts
that witness, and `use [= run_forever]` contradicts termination at that fuel.
Use `show_state` or `show_cases` inside this script to inspect the reasoning.
For other proofs, `grind?` suggests a smaller theorem list, and
`set_option trace.grind.ematch.instance true in` displays theorem instantiations.

For further reading, see the official documentation on
[library annotations](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Annotating-Libraries-for--grind/),
[E-matching and pattern constraints](https://lean-lang.org/doc/reference/latest/The--grind--tactic/E___matching/),
and [interactive mode](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Interactive-Mode/).
These are the latest reference pages; the features used here were also checked
against the installed Lean v4.35.0 source and compiled with that toolchain.

Import `MiniForth.Grind.Rules` to use the common annotations, or `MiniForth.Grind`
to load the full automated lesson. The umbrella `MiniForth` import includes both
sets of lessons, so `lake build` checks them together. The original lesson modules
themselves do not import the automation rules.

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
