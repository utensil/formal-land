import Verso
import VersoManual

open Lean.MessageSeverity

-- #check Verso.Doc.Inline.math
-- #check Verso.Doc.MathMode

open Verso Doc Elab in
@[code_block_expander latex]
def Manual.latex : CodeBlockExpander
  | _args, str => do
    return #[(← `(Doc.Block.para #[Doc.Inline.math Doc.MathMode.display s!"{$str}"]))]

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Math" =>
%%%
htmlSplit := .never
tag := "math"
%%%

Inline math:

$`E=mc^2`

Display math:

$$`E=mc^2`

❌ But no support for multiline math yet.

The following is a workaround inspired by [lecopivo/scientific-computing-lean](https://github.com/lecopivo/scientific-computing-lean/blob/ae7f1f6359465687136a9e75e0c83a1ef19525c2/ScientificComputingInLean/Meta/Latex.lean):

```latex
f'(x) = \lim_{h → 0} \frac{f(x+h) - f(x)}{h}
```
