import VersoManual

open Lean.MessageSeverity

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

