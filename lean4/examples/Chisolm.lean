import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.Tactic
-- import Mathlib.Util.Superscript
-- import Mathlib.Data.Matrix.Notation

variable {R : Type _}

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

variable [Invertible (2 : R)]

variable [Invertible (2 : CliffordAlgebra Q)]

variable (u v w : CliffordAlgebra Q)

local notation "𝒢" => algebraMap R (CliffordAlgebra Q)

lemma mul_eq_half_add_half_sub : u * v = ⅟2 * (u * v + v * u) + ⅟2 * (u * v - v * u) := by
  calc
    u * v = 1 * (u * v)                                             := by rw [one_mul]
        _ = (⅟2 * 2) * (u * v)                                      := by rw [invOf_mul_self']
        _ = ⅟2 * (2 * (u * v))                                      := by rw [mul_assoc]
        _ = ⅟2 * (u * v + u * v)                                    := by rw [←two_mul]
        _ = ⅟2 * ((u * v + v * u) + (u * v - v * u))                := by rw [add_add_sub_cancel]
        _ = ⅟2 * (u * v + v * u) + ⅟2 * (u * v - v * u)             := by rw [mul_add]
  done

#check mul_eq_half_add_half_sub

/-!
  Axiom 1. G is a ring with unit.
  The additive identity is called 0 and the multiplicative identity is called 1.
-/
#check CliffordAlgebra.instRing
example : 0 + u = u := by rw [zero_add]
example : u + 0 = u := by rw [add_zero]
example : 1 * u = u := by rw [one_mul]
example : u * 1 = u := by rw [mul_one]

/-!
  Axiom 2. G contains a ~~field~~ring G0 of characteristic zero which includes 0 and 1.
-/
-- [Field R]
-- [DivisionRing R] [CharZero R]

local notation "𝟘" => (0 : CliffordAlgebra Q)
local notation "𝟙" => (1 : CliffordAlgebra Q)

#check 𝒢
#check 𝟘
#check 𝟙


/-!
  Axiom 3. G contains a subset G1 closed under addition, and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
-/
#check M

local notation "ι" => CliffordAlgebra.ι Q

example (r : R) (u : M)  : 𝒢 r * ι u = ι u * 𝒢 r := by rw [@Algebra.commutes]

example (r : R) (u : M) : ∃ w : M, ι w = 𝒢 r * ι u := by
  use (r • u)
  rw [map_smul, Algebra.smul_def, Algebra.commutes]

/-!
  Axiom 4. The square of every vector is a scalar.
-/
#check CliffordAlgebra.ι_sq_scalar

-- def square {Gn G: Type*} (m : Gn) : G
-- | M.mk m => (ι m)^2

local instance hasCoeCliffordAlgebraRing : Coe R (CliffordAlgebra Q) := ⟨𝒢⟩
local instance hasCoeCliffordAlgebraModule : Coe M (CliffordAlgebra Q) := ⟨ι⟩

set_option quotPrecheck false
local notation x "²" => (↑x : CliffordAlgebra Q)^2

theorem ι_sq_scalar (m : M) : m² = Q m := by
  rw [pow_two, CliffordAlgebra.ι_sq_scalar]
  done

-- local macro_rules
-- | `($x ^ $y) => `(HPow.hPow $x $y)

-- #check 𝒢^n

-- syntax (name := cliffordNotation) "𝒢[" term "]" : term

#check CliffordAlgebra.gradedAlgebra

-- local notation "𝒢" => CliffordAlgebra

-- local macro_rules
-- | `($x ^ $y) => `(HPow.hPow $x $y)

-- -- #check 𝒢^n

-- -- syntax (name := cliffordNotation) "𝒢[" term "]" : term

-- namespace GradedAlgebra

-- local notation g "⟦" r "⟧'" => GradedAlgebra.proj g r

-- -- #check GradedAlgebra.proj G.ι G 0

-- -- #check G⟦0⟧

-- end GradedAlgebra



