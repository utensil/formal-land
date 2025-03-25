import Mathlib.Algebra.Group.Nat.Defs

namespace String

def fillLeft (s : String) (c : Char) (n : Nat)  : String :=
  "".pushn c (n - s.length) ++ s

end String

namespace Float

def intPart (f : Float) : String :=
  String.join <| f.toString.splitOn "." |>.take 1

def toDecimal (f : Float) (precision : Nat) : String :=
  let int := f.round
  let intStr := int.intPart
  let fraction := ((f-int) * (10 ^ precision).toFloat).abs.round
  let fractionStr := fraction.intPart.fillLeft '0' precision
  if precision > 0 then s!"{intStr}.{fractionStr}" else intStr

end Float


/-- info: "3.11235" -/
#guard_msgs in
#eval 3.1123456.toDecimal 5

/-- info: "-123.4567890" -/
#guard_msgs in
#eval (-123.456789).toDecimal 7

/-- info: "0.0000100" -/
#guard_msgs in
#eval (0.00001).toDecimal 7

/-- info: "-0.3000000" -/
#guard_msgs in
#eval (-0.3).toDecimal 7

/-- info: "-1" -/
#guard_msgs in
#eval (-1.23).toDecimal 0
