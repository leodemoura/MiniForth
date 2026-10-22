import MiniForth.Quotation
import MiniForth.PrettyPrinter

/-!
# Writing and reading MiniForth inside Lean

`Quotation` defines the embedded notation and its elaboration into syntax trees.
`PrettyPrinter` renders those trees with the same notation in goals and messages.
Import this module for both directions.
-/

-- open MiniForth
-- set_option pp.miniForth false

#check [forthProgram|
: SQUARE DUP * ;
: CUBE DUP SQUARE * ;
: SUM-OF-SQUARES SQUARE SWAP SQUARE + ;
3 4 SUM-OF-SQUARES
]
