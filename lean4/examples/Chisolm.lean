import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
-- import Mathlib.Data.Matrix.Notation

variable {R : Type _}

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

variable [Invertible (2 : R)]

variable (u v w : CliffordAlgebra Q)

local notation "𝒢" => algebraMap R (CliffordAlgebra Q)

local notation "𝟙" => 𝒢 1
local notation "𝟚" => 𝒢 2
local notation "⅟𝟚" => 𝒢 ⅟2

lemma mul_eq_half_add_half_sub : u * v = ⅟𝟚 * (u * v + v * u) + ⅟𝟚 * (u * v - v * u) := by
  calc
    u * v = 𝟙 * (u * v)                                             := by rw [map_one, one_mul]
        _ = 𝒢 (⅟2 * 2) * (u * v)                                    := by rw [invOf_mul_self']
        _ = ⅟𝟚 * 𝟚 * (u * v)                                        := by rw [map_mul]
        _ = ⅟𝟚 * 2 * (u * v)                                        := by rw [map_ofNat]
        _ = ⅟𝟚 * (2 * (u * v))                                      := by rw [mul_assoc]
        _ = ⅟𝟚 * (u * v + u * v)                                    := by rw [←two_mul]
        _ = ⅟𝟚 * ((u * v + v * u) + (u * v - v * u))                := by rw [add_add_sub_cancel]
        _ = ⅟𝟚 * (u * v + v * u) + ⅟𝟚 * (u * v - v * u)             := by rw [mul_add]
  done

#check mul_eq_half_add_half_sub

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



