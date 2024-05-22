import Mathlib.Algebra.Group.Nat

namespace Float

def intPart (f : Float) : String :=
  String.join <| f.toString.splitOn "." |>.take 1

def toDecimal (f : Float) (precision : Nat) : String :=
  let int := f.round
  let intStr := int.intPart
  let fraction := ((f-int) * (10 ^ precision).toFloat).abs.round
  let fractionStr := if fraction != 0.0 then fraction.intPart else ("".pushn '0' precision)
  if precision > 0 then s!"{intStr}.{fractionStr}" else intStr

end Float

/-
"3.11235"
-/
#eval 3.1123456.toDecimal 5

/-
"-123.4567890"
-/
#eval (-123.456789).toDecimal 7

/-
"0.0000000"
-/
#eval 0.0.toDecimal 7

/-
"-0.3000000"
-/
#eval (-0.3).toDecimal 7

/-
"-1"
-/
#eval (-1.23).toDecimal 0
