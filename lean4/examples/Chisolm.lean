import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.Tactic
-- import Mathlib.Util.Superscript
-- import Mathlib.Data.Matrix.Notation

set_option quotPrecheck false

variable {R : Type _}

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

variable [Invertible (2 : R)]

variable [Invertible (2 : CliffordAlgebra Q)]

variable (u v w : CliffordAlgebra Q)

local instance hasCoeCliffordAlgebraRing : Coe R (CliffordAlgebra Q) := ⟨algebraMap R (CliffordAlgebra Q)⟩
local instance hasCoeCliffordAlgebraModule : Coe M (CliffordAlgebra Q) := ⟨CliffordAlgebra.ι Q⟩

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

-- local notation "𝒢" => algebraMap R (CliffordAlgebra Q)
-- #check 𝒢
#check 𝟘
#check 𝟙


/-!
  Axiom 3. G contains a subset G1 closed under addition, and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
-/
#check M

-- local notation "ι" => CliffordAlgebra.ι Q

-- local notation "∘" => CliffordAlgebra.mul

-- example (r : R) (u : M)  : r ∘ u = u ∘ r := by rw [@Algebra.commutes]
-- local notation "*" => fun x y => (CliffordAlgebra Q).mul ↑x ↑y

example (r : R) (u : M) : (r * u : CliffordAlgebra Q) = u * r := by rw [@Algebra.commutes]

example (r : R) (u : M) : ∃ w : M, w = (r * u : CliffordAlgebra Q) := by
  use (r • u)
  rw [map_smul, Algebra.smul_def, Algebra.commutes]

/-!
  Axiom 4. The square of every vector is a scalar.
-/
#check CliffordAlgebra.ι_sq_scalar

-- def square {Gn G: Type*} (m : Gn) : G
-- | M.mk m => (ι m)^2


local notation x "²" => (↑x : CliffordAlgebra Q)^2

theorem ι_sq_scalar (m : M) : m² = Q m := by
  rw [pow_two, CliffordAlgebra.ι_sq_scalar]
  done

/-！
  Axiom 5. The inner product is nondegenerate.

TODO: Wait to see if this is necessary and what's the weaker condition.
-/

/-!
  Axiom 6. If G0 = G1, then G = G0. TODO: Wait to see if this is necessary and what's the weaker condition.
  
  Otherwise, G is the direct sum of all the Gr.
-/

#check CliffordAlgebra.GradedAlgebra.ι
#check CliffordAlgebra.GradedAlgebra.ι_apply

-- def 𝒢ᵣ (v : M) (i : ℕ) := CliffordAlgebra.GradedAlgebra.ι Q v i

#check GradedAlgebra.proj
-- #check CliffordAlgebra.proj

-- invalid occurrence of universe level 'u_3' at '𝒢ᵣ', it does not occur at the declaration type, nor it is explicit universe level provided by the user, occurring at expression
--   sorryAx.{u_3} (?m.443921 _uniq.442570 _uniq.443000 _uniq.443430 mv i)
-- at declaration body
--   fun {R : Type u_1} {M : Type u_2} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}
--       (mv : CliffordAlgebra Q) (i : ℕ) =>
--     sorryAx (?m.443921 _uniq.442570 _uniq.443000 _uniq.443430 mv i)
-- def 𝒢ᵣ (mv : CliffordAlgebra Q) (i : ℕ) := sorry

-- variable {ι : Type _} [DecidableEq ι] [AddMonoid ι]
-- variable (𝒜 : ι → Submodule R (CliffordAlgebra Q))
variable (𝒜 : ℕ → Submodule R (CliffordAlgebra Q))

def 𝒢ᵣ (mv : CliffordAlgebra Q) (i : ℕ) : CliffordAlgebra Q := GradedAlgebra.proj (CliffordAlgebra.evenOdd Q) i mv

#check List

-- (fun xs i => true)
--  (CliffordAlgebra Q → ℕ → Prop) 
instance instGetElemByGradeCliffordAlgebra : GetElem (CliffordAlgebra Q) ℕ (CliffordAlgebra Q) (fun _mv _i => true) := {
  getElem := fun mv i _h => 𝒢ᵣ mv i
}

example (mv : CliffordAlgebra Q) (i : ℕ) : mv[i] = mv[i] := rfl

#check CoeFun

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



