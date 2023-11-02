import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

set_option trace.Meta.synthInstance true
set_option synthInstance.checkSynthOrder false

#check Monoid.mk

whatsnew in
lemma demo {α : Type} [Monoid α] (a b : α) : a * b = a * b := by rfl

#synth Module ℤ ℤ

#check RingHomClass.mk -- map_add, map_zero, toMonoidHomClass

#check MonoidHomClass.mk -- map_one, toMulHomClass

#check MulHomClass.mk -- map_mul, toFunLike

#check FunLike.mk -- coe, coe_injective'

#check RingHom.mk -- map_zero', map_add', toMonoidHom

#check MonoidHom.mk -- map_mul', toOneHom

#check OneHom.mk -- map_one', toFun

#check Algebra.mk -- toSMul, toRingHom, commutes', smul_def'

#check FreeAlgebra.Rel

example [CommSemiring R] [Semiring A] [Algebra R A] (a b : A): a + b = b + a := by
  ring_nf
  sorry
  
