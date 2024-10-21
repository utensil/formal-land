-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Overloading.20infixes.3F
import Mathlib.Tactic.Common
import Mathlib.Util.Notation3

notation3:70 x " ⊗₁ " y => x * y
infix:70 " ⊗₂ " => Mul.mul

variable (Φ : Type) [Mul Φ] (φ ψ : Φ)

/-- info: φ ⊗₁ ψ : Φ -/
#guard_msgs in #check φ ⊗₁ ψ

/-- info: φ ⊗₂ ψ : Φ -/
#guard_msgs in #check φ ⊗₂ ψ
