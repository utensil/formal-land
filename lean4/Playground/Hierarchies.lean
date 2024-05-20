import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Algebra.Free

-- set_option trace.Meta.synthInstance true
-- set_option synthInstance.checkSynthOrder false

#check Monoid.mk

whatsnew in
example {α : Type} [Monoid α] (a b : α) : a * b = a * b := by rfl

#synth Module ℤ ℤ

#check RingHomClass.mk -- map_add, map_zero, toMonoidHomClass

#check MonoidHomClass.mk -- map_one, toMulHomClass

#check MulHomClass.mk -- map_mul, toFunLike

#check FunLike

-- #check FunLike.mk -- coe, coe_injective'

#check RingHom.mk -- map_zero', map_add', toMonoidHom

#check MonoidHom.mk -- map_mul', toOneHom

#check OneHom.mk -- map_one', toFun

#check Algebra.mk -- toSMul, toRingHom, commutes', smul_def'

#check FreeAlgebra.Rel

example [CommSemiring R] [Semiring A] [Algebra R A] (a b : A): a + b = b + a := by
  ring_nf
  sorry

#check CliffordAlgebra.ι

#check CliffordAlgebra.lift

#check algebraMap

#check AlgHom

#check CliffordAlgebra.ι_comp_lift

-- #check f₁ ∘ₗ f₂

#check CliffordAlgebra.lift_unique

#check ExteriorAlgebra

#check TensorAlgebra.toClifford

#check Module.Dual

#check Module.Free

#check Module.Finite

#check LinearMap.module

#check star

postfix:max "ᘁ" => star

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20How.20to.20find.20the.20detailed.20definition.20of.20a.20.22notation.22.20.3F

universe u v
variable (n2 : Type u) (α2 : Type v) [DivisionMonoid (Matrix n2 n2 α2)] (A B : Matrix n2 n2 α2)

/-
[Meta.synthInstance] ✅ HMul (Matrix n2 n2 α2) (Matrix n2 n2 α2) (Matrix n2 n2 α2) ▼
  [] new goal HMul (Matrix n2 n2 α2) (Matrix n2 n2 α2) _tc.0 ▼
    [instances] #[@instHMul, @Matrix.instHMulMatrixMatrixMatrix]
-/
#check A * B

theorem mul_inv_rev2 : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by sorry

#check Prop

#check Bool

-- TOD: PR
#check QuadraticForm.associated_left_inverse
#check QuadraticForm.associated_rightInverse

#check FreeMagma.rec

#check FreeMonoid

#check FreeSemigroup

#check FreeRing

--#check FreeModule

#check FreeAlgebra.Rel

example {R A : Type} [Monoid α] (a b : α) : a * b = a * b := by rfl

#check RingQuot.mk

#check RingQuot.Rel

#check Ideal

#check TensorAlgebra


-- chore(Algebra/FreeAlgebra): fix comments
