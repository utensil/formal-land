import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic
-- import Mathlib.Util.Superscript
-- import Mathlib.Data.Matrix.Notation

open FiniteDimensional (finrank finrank_eq_card_basis finrank_directSum )

set_option quotPrecheck false

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

-- abbrev 𝒢 := CliffordAlgebra Q
-- abbrev Cl := CliffordAlgebra Q
-- def Cl := CliffordAlgebra Q

/-
Cl.{u_2, u_1} {R : Type u_1} {M : Type u_2} [inst✝ : CommRing R] [inst✝¹ : AddCommGroup M] [inst✝² : Module R M]
  {Q : QuadraticForm R M} : Type (max u_2 u_1)
-/
-- #check Cl

-- local notation "𝐶𝑙" => CliffordAlgebra Q
-- local notation "𝒢" => CliffordAlgebra Q
-- local notation "𝔊" => CliffordAlgebra Q
-- local notation:50 A " =[" T:50 "] " B:50 => @Eq T A B
-- local notation:50 A "=ₐ" B:50 => @Eq 𝐶𝑙 A B

local notation "Cl" => CliffordAlgebra Q
local notation:50 A "=" B:50 ":" T:50 => @Eq T A B

example (u v: M) : ∃ w : M, w = u + v : Cl := by
  use (u + v)
  rw [map_add]

example (r : R) (u : M) : r * u = u * r : Cl := by rw [@Algebra.commutes]

example (r : R) (u : M) : ∃ w : M, w = r * u : Cl := by
  use (r • u)
  rw [map_smul, Algebra.smul_def, Algebra.commutes]

/-!
  Axiom 4. The square of every vector is a scalar.
-/
#check CliffordAlgebra.ι_sq_scalar

-- def square {Gn G: Type*} (m : Gn) : G
-- | M.mk m => (ι m)^2


local notation x "²" => (x : Cl)^2

theorem ι_sq_scalar (m : M) : m² = Q m : Cl := by
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
instance instGetElemByGradeCliffordAlgebra : GetElem (CliffordAlgebra Q) ℕ (CliffordAlgebra Q) (fun _mv i => i < Module.rank R (CliffordAlgebra Q)) := {
  getElem := fun mv i _h => 𝒢ᵣ mv i
}

example (mv : CliffordAlgebra Q) (i : ℕ) (h : i < Module.rank R (CliffordAlgebra Q)) : mv[i] = mv[i] := rfl

#check CoeFun

#check Module.Finite

#check Submodule.span

#check Module.rank R M

#check Module.rank R (CliffordAlgebra Q)

#check Algebra.adjoin

#check Subsemiring.closure

#check Algebra.adjoin_eq

#check Algebra.adjoin_eq_range_freeAlgebra_lift

example (c : ℂ) : c = c := rfl

#check CliffordAlgebraComplex.ofComplex

#check Module.rank ℝ (CliffordAlgebra CliffordAlgebraComplex.Q)

example : Cardinal.mk ℝ = Cardinal.continuum := by
  simp only [Cardinal.mk_real]

example : Module.rank ℝ ℝ = 1 := by
  simp only [rank_self]

example : Module.rank ℝ ℂ = 2 := by
  simp only [Complex.rank_real_complex]

#check RingHom.Finite

-- local instance : Module.Finite ℝ ℂ := by
--   apply Complex.finite_real_complex

-- instance instFiniteCliffordAlgebraComplex : Module.Finite ℝ (CliffordAlgebra CliffordAlgebraComplex.Q) := sorry

noncomputable def basisOneI : Basis (Fin 2) ℝ (CliffordAlgebra CliffordAlgebraComplex.Q) :=
  Basis.ofEquivFun
    { toFun := fun mv =>
      let z := CliffordAlgebraComplex.toComplex mv
      ![z.re, z.im]
      invFun := fun c => CliffordAlgebraComplex.ofComplex (c 0 + c 1 • Complex.I)
      left_inv := fun z => by simp
      right_inv := fun c => by
        ext i
        fin_cases i <;> simp
      map_add' := fun z z' => by simp
      map_smul' := fun c z => by simp }

example : finrank ℝ (CliffordAlgebra CliffordAlgebraComplex.Q) = 2 := by
  rw [finrank_eq_card_basis basisOneI, Fintype.card_fin]
  done

#check CliffordAlgebraComplex.equiv

universe uA

#check AlgEquiv.toLinearEquiv_refl
#check FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
/-
LinearEquiv.finrank_eq.{u_3, u_2, u_1} {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst✝ : Ring R]
  [inst✝¹ : AddCommGroup M] [inst✝² : AddCommGroup M₂] [inst✝³ : Module R M] [inst✝⁴ : Module R M₂] (f : M ≃ₗ[R] M₂) :
  finrank R M = finrank R M₂
-/
#check LinearEquiv.finrank_eq

#check CommRing

local notation "Clℂ" => CliffordAlgebra CliffordAlgebraComplex.Q

lemma finrank_eq (R: Type uR) (A B: Type uA) [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] :
  (A ≃ₐ[R] B) → finrank R A = finrank R B := fun ha => LinearEquiv.finrank_eq ha.toLinearEquiv
--   done

example : finrank ℝ Clℂ = finrank ℝ ℂ := by
  rw [finrank_eq ℝ Clℂ ℂ CliffordAlgebraComplex.equiv]

example : finrank ℝ Clℂ = finrank ℝ ℂ := LinearEquiv.finrank_eq CliffordAlgebraComplex.equiv.toLinearEquiv
  
--   done


-- example (n : ℕ) : Cardinal.mk (Vector ℝ n) = n := by
--   simp only [Cardinal.mk_vector]
--   done

-- #check Cardinal.mk_vector

-- example (c : ℂ) : (CliffordAlgebraComplex.ofComplex c)[0] = 1 := rfl

-- example : Module.rank R (CliffordAlgebra Q) = 2^(Module.rank R M) := sorry


#check DirectSum.GradeZero.module
#check finrank_directSum

#check DirectSum.decomposeRingEquiv (CliffordAlgebra.evenOdd Q)

#check LinearEquiv.ofFinrankEq

example : finrank R (CliffordAlgebra Q) = 2^(finrank R M) := by
  -- conv_lhs => rw [finrank_directSum]
  rw [← Nat.sum_range_choose]
  have 
  done