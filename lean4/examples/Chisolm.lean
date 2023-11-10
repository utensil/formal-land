import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.Tactic
-- import Mathlib.Util.Superscript
-- import Mathlib.Data.Matrix.Notation

variable {R : Type _}

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

variable [Invertible (2 : R)]

variable (u v w : CliffordAlgebra Q)

local notation "𝒢" => algebraMap R (CliffordAlgebra Q)

local notation "𝟘" => 𝒢 0
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

/-!
  Axiom 1. G is a ring with unit.
  The additive identity is called 0 and the multiplicative identity is called 1.
-/
#check CliffordAlgebra.instRing
example : 𝟘 + u = u := by rw [map_zero, zero_add]
example : u + 𝟘 = u := by rw [map_zero, add_zero]
#check 𝟙
example : 𝟙 * u = u := by rw [map_one, one_mul]
example : u * 𝟙 = u := by rw [map_one, mul_one]

/-!
  Axiom 2. G contains a ~~field~~ring G0 of characteristic zero which includes 0 and 1.
-/
-- [Field R]
-- [DivisionRing R] [CharZero R]
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



