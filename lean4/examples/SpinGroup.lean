/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao
-/
-- This file is mathported from https://github.com/leanprover-community/mathlib/pull/16040/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Tactic

-- TODO: remove when in Mathlib
set_option autoImplicit false
-- set_option trace.Meta.synthInstance true

-- TODO: decide what to do with this
#align_import main

/-!
# The Pin group and the Spin group

In this file we define `lipschitz`, `pinGroup` and `spinGroup` and show they form a group.

## Main definitions

* `lipschitz`: the Lipschitz group with a quadratic form.
* `pinGroup`: the Pin group defined as the infimum of `lipschitz` and `unitary`.
* `spinGroup`: the Spin group defined as the infimum of `pinGroup` and `clifford.even`.

## Implementation Notes

Here are some discussion about the latent ambiguity of definition :
https://mathoverflow.net/q/427881/172242 and https://mathoverflow.net/q/251288/172242

The definition of the Lipschitz group `{𝑥 ∈ 𝐶𝑙(𝑉,𝑞) │ 𝑥 𝑖𝑠 𝑖𝑛𝑣𝑒𝑟𝑡𝑖𝑏𝑙𝑒 𝑎𝑛𝑑 𝑥𝑣𝑥⁻¹∈ 𝑉}` is given by:
• Fulton, W. and Harris, J., 2004. Representation theory. New York: Springer, p.chapter 20.
• https://en.wikipedia.org/wiki/Clifford_algebra#Lipschitz_group
But they presumably form a group only in finite dimensions. So we define `lipschitz` with closure of
all the elements in the form of `ι Q m`, and we show this definition is at least as large as the
other definition (See `mem_lipschitz_conj_act_le` and `mem_lipschitz_involute_le`). The reverse
statement presumably being true only in finite dimensions.

## TODO

Try to show the reverse statement is true in finite dimensions.
-/


variable {R : Type*} [CommRing R] [Nontrivial R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

section Pin

open CliffordAlgebra MulAction

open scoped Pointwise

-- begin doesn't belong to this file

#check equivExterior
#check ExteriorAlgebra.algebraMapInv
#check instNontrivialCliffordAlgebra
variable (m : M) [Invertible (2 : R)] in
#check ExteriorAlgebra.algebraMapInv ((equivExterior Q).toFun (ι Q m))

def inv_of_inv_sq' (m : M) [Invertible (ι Q m)] [Invertible (2 : R)] : Invertible ((ι Q m) * (ι Q m)) := {
  invOf := ⅟(ι Q m) * ⅟(ι Q m),
  invOf_mul_self := by
    convert_to ⅟(ι Q m) * (⅟(ι Q m) * (ι Q m)) * (ι Q m) = 1
    . simp only [mul_assoc]
    . simp only [invOf_mul_self', mul_one],
  mul_invOf_self := by
    convert_to (ι Q m) * ((ι Q m) * ⅟(ι Q m)) * ⅟(ι Q m) = 1
    . simp only [mul_assoc]
    . simp only [mul_invOf_self', mul_one]
}

#check inv_of_inv_sq'

def invertible_of_invertible_ι' (m : M) [Invertible (ι Q m)] [Invertible (2 : R)] : Invertible (algebraMap _ _ (Q m) : CliffordAlgebra Q) := {
  invOf := ⅟ (ι Q m) * ⅟ (ι Q m),
  invOf_mul_self := by
    rw [← ι_sq_scalar]
    exact (inv_of_inv_sq' m).invOf_mul_self,
  mul_invOf_self := by
    rw [← ι_sq_scalar]
    exact (inv_of_inv_sq' m).mul_invOf_self
}

def CliffordAlgebra.toScalar [Invertible (2 : R)] (x : CliffordAlgebra Q) : R :=
  ExteriorAlgebra.algebraMapInv ((equivExterior Q).toFun x)


variable [Invertible (2 : R)] (r : R) in
#check CliffordAlgebra.toScalar (algebraMap _ _ r)

lemma algebraMap_toScalar [Invertible (2 : R)] (r : R) :
  CliffordAlgebra.toScalar (algebraMap _ _ r : CliffordAlgebra Q) = r :=
  by simp [CliffordAlgebra.toScalar]

-- begin eric PR code

section

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- If there is a linear map `f : A →ₗ[R] B` that preserves `1`, then `algebraMap R B r` is invertible when `algebraMap R A r` is. -/
abbrev algebraMapMap (f : A →ₗ[R] B) (hf : f 1 = 1) {r : R} (h : Invertible (algebraMap R A r)) :
    Invertible (algebraMap R B r) where
  invOf := f ⅟(algebraMap R A r)
  invOf_mul_self := by rw [←Algebra.commutes, ←Algebra.smul_def, ←map_smul, Algebra.smul_def, mul_invOf_self, hf]
  mul_invOf_self := by rw [←Algebra.smul_def, ←map_smul, Algebra.smul_def, mul_invOf_self, hf]

end

-- end eric PR code

-- begin eric code

def inv_of_inv_sq (m : M) [Invertible (ι Q m)] [Invertible (2 : R)] : Invertible ((ι Q m) * (ι Q m)) :=
  Invertible.mul ‹_› ‹_›

def inv_algebraMap_of_inv_ι (m : M) [Invertible (ι Q m)] [Invertible (2 : R)] : Invertible (algebraMap _ _ (Q m) : CliffordAlgebra Q) :=
  Invertible.copy (inv_of_inv_sq m) _ (ι_sq_scalar _ _).symm

def inv_of_inv_ι (m : M) [Invertible (ι Q m)] [Invertible (2 : R)] : Invertible (Q m) :=
  letI : Invertible (algebraMap _ (CliffordAlgebra Q) (Q m)) :=
    (Invertible.mul ‹Invertible (ι Q m)› ‹Invertible (ι Q m)›).copy  _ (ι_sq_scalar _ _).symm
  letI bar : Invertible (algebraMap _ (ExteriorAlgebra R M) (Q m)) := {
    invOf := equivExterior Q ⅟(algebraMap _ (CliffordAlgebra Q) (Q m))
    invOf_mul_self := by
      dsimp
      rw [←Algebra.commutes, ←Algebra.smul_def, ←map_smul, Algebra.smul_def, mul_invOf_self, changeForm_one]
    mul_invOf_self := by
      dsimp
      rw [←Algebra.smul_def, ←map_smul, Algebra.smul_def, mul_invOf_self, changeForm_one]
  }
  (bar.map ExteriorAlgebra.algebraMapInv).copy _ (by simp)

-- end eric code


#align invertible_of_invertible_ι inv_of_inv_ι

-- restore the lean3 behavior
macro_rules | `($x * $y) => `(@HMul.hMul _ _ _ instHMul $x $y)

-- local instance : Coe (CliffordAlgebra Q)ˣ (CliffordAlgebra Q) :=
--   ⟨Units.val⟩

-- end doesn't belong to this file

/-- `lipschitz` is the subgroup closure of all the elements in the form of `ι Q m` where `ι`
is the canonical linear map `M →ₗ[R] clifford_algebra Q`. -/
def lipschitz (Q : QuadraticForm R M) :=
  Subgroup.closure (Units.val ⁻¹' Set.range (ι Q) : Set (CliffordAlgebra Q)ˣ)
#align lipschitz lipschitz

set_option pp.analyze true in
variable {x : (CliffordAlgebra Q)ˣ} [Invertible (2 : R)] (hx : x ∈ lipschitz Q) in
#check @Subgroup.closure_induction'' _ _ _ _ _ hx _ _ _ _

#check (ι Q)

#check LinearMap.range (ι Q)

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/dot.20notation.20with.20Multiplicative
-- #check (ι Q).range

-- #check invertible_of_invertible_ι

variable [Invertible (2 : R)] (z: M) [Invertible (ι Q z)] in
#check inv_of_inv_ι z

example [Invertible (2 : R)] (z: M) (x: (CliffordAlgebra Q)ˣ) (hz : (ι Q z) = x) : Invertible (Q z) := by
  haveI := x.invertible
  haveI : Invertible (ι Q z) := by rwa [hz]
  exact inv_of_inv_ι z

variable [Invertible (2 : R)] (z b: M) [Invertible (ι Q z)] [Invertible (Q z)] in
#check ι_mul_ι_mul_invOf_ι Q z b

#check @Algebra.toSMul

set_option trace.Meta.synthInstance true in
variable {x : (CliffordAlgebra Q)ˣ} [Invertible (2 : R)] (hx : x ∈ lipschitz Q) in
#check ConjAct.toConjAct x • LinearMap.range (ι Q)

#check Exists.imp

set_option synthInstance.maxHeartbeats 25000 in
/-- If x is in `lipschitz Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions.-/
theorem mem_lipschitz_conjAct_le {x : (CliffordAlgebra Q)ˣ} [Invertible (2 : R)]
    (hx : x ∈ lipschitz Q) : ConjAct.toConjAct x • LinearMap.range (ι Q) ≤ LinearMap.range (ι Q) := by
  unfold lipschitz at hx
  apply Subgroup.closure_induction'' hx
  · rintro x ⟨a, ha⟩ y ⟨z, ⟨⟨b, hb⟩, hz⟩⟩
    rw [LinearMap.mem_range]
    have := x.invertible
    have : Invertible (ι Q a) := by rwa [ha]
    have : Invertible (Q a) := inv_of_inv_ι a
    simp only [HSMul.hSMul, SMul.smul, DistribMulAction.toLinearMap_apply, ConjAct.ofConjAct_toConjAct,
                SetLike.mem_coe, LinearMap.mem_range] at hz -- diff
    subst hb
    suffices : ∃ y : M, ι Q y = ι Q a * ι Q b * ⅟ (ι Q a)
    . simp_all only [invOf_units]
    . rw [ι_mul_ι_mul_invOf_ι Q a b]
      use ((⅟ (Q a) * QuadraticForm.polar Q a b) • a - b)
  · rintro x ⟨a, ha⟩ y ⟨z, ⟨⟨b, hb⟩, hz⟩⟩
    rw [LinearMap.mem_range]
    have := x.invertible
    have : Invertible (ι Q a) := by rwa [ha]
    have : Invertible (Q a) := inv_of_inv_ι a
    simp [HSMul.hSMul, SMul.smul, DistribMulAction.toLinearMap_apply, ConjAct.ofConjAct_toConjAct,
                ConjAct.toConjAct_inv, inv_inv] at hz -- diff
    subst hb
    suffices : ∃ y : M, ι Q y = ⅟ (ι Q a) * ι Q b * ι Q a
    . simp_all only [invOf_units]
    . rw [invOf_ι_mul_ι_mul_ι Q a b]
      use ((⅟ (Q a) * QuadraticForm.polar Q a b) • a - b)
  · simp only [ConjAct.toConjAct_one, (one_smul _ (LinearMap.range (ι Q))), le_refl]
  · intro x y hx1 hy1 z hz
    simp only [ConjAct.toConjAct_mul] at hz
    suffices (ConjAct.toConjAct x * ConjAct.toConjAct y) • LinearMap.range (ι Q) ≤ LinearMap.range (ι Q) by
      exact this hz

    rintro m ⟨a, ⟨b, hb⟩, ha⟩
    simp only [HSMul.hSMul, SMul.smul, DistribMulAction.toLinearMap_apply, Units.val_mul, mul_inv_rev] at ha
    subst hb
    have hb : ↑x * (↑y * (ι Q b) * ↑y⁻¹) * ↑x⁻¹ = m := by
      simp [← ha, ConjAct.toConjAct_mul, ConjAct.units_smul_def, mul_assoc]
    have hy2 : ↑y * (ι Q) b * ↑y⁻¹ ∈ ConjAct.toConjAct y • LinearMap.range (ι Q) := by
      simp only [HSMul.hSMul, SMul.smul, exists_exists_eq_and, exists_apply_eq_apply, Submodule.mem_map,
        LinearMap.mem_range, DistribMulAction.toLinearMap_apply, ConjAct.ofConjAct_toConjAct]
    specialize hy1 hy2
    have hx2 : ↑x * (↑y * (ι Q) b * ↑y⁻¹) * ↑x⁻¹ ∈ ConjAct.toConjAct x • LinearMap.range (ι Q) :=
      by
      simp only [HSMul.hSMul, SMul.smul, Units.mul_left_inj, Units.mul_right_inj, exists_exists_eq_and,
        Submodule.mem_map, LinearMap.mem_range, DistribMulAction.toLinearMap_apply,
        ConjAct.ofConjAct_toConjAct]
      exact hy1
    specialize hx1 hx2
    rwa [hb] at hx1
#align mem_lipschitz_conj_act_le mem_lipschitz_conjAct_le

#print mem_lipschitz_conjAct_le

/-- This is another version of `mem_lipschitz_conj_act_le` which uses `involute`.-/
theorem mem_lipschitz_involute_le {x : (CliffordAlgebra Q)ˣ} [Invertible (2 : R)]
    (hx : x ∈ lipschitz Q) (y : M) : involute ↑x * ι Q y * ↑x⁻¹ ∈ LinearMap.range (ι Q) :=
  by
  revert y
  refine' @Subgroup.closure_induction'' _ _ _ _ _ hx _ _ _ _
  · rintro x ⟨z, hz⟩ y
    letI := x.invertible
    letI : Invertible (ι Q z) := by rwa [hz]
    rw [LinearMap.mem_range, ← invOf_units x]
    suffices ∃ y_1 : M, (ι Q) y_1 = -ι Q z * (ι Q) y * ⅟ (ι Q z)
      by
      convert this
      ext1
      congr
      · rw [← hz, involute_ι]
      · exact hz.symm
      · exact Subsingleton.helim (congr_arg Invertible hz.symm) _ _
    letI := invertibleOfInvertibleι Q z
    refine'
      ⟨-((⅟ (Q z) * QuadraticForm.polar Q z y) • z - y), by
        simp only [map_neg, neg_mul, ι_mul_ι_mul_inv_of_ι Q z y]⟩
  · rintro x ⟨z, hz⟩ y
    letI := x.invertible
    letI : Invertible (ι Q z) := by rwa [hz]
    letI := invertibleNeg (ι Q z)
    letI := Invertible.map (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q) ↑x
    rw [inv_inv, LinearMap.mem_range, ← invOf_units x, map_invOf]
    suffices ∃ y_1 : M, (ι Q) y_1 = -⅟ (ι Q z) * (ι Q) y * ι Q z
      by
      convert this
      ext1
      congr
      · rw [← invOf_neg]
        apply invertible_unique
        rw [← hz, involute_ι]
      · exact hz.symm
    letI := invertibleOfInvertibleι Q z
    refine'
      ⟨-((⅟ (Q z) * QuadraticForm.polar Q z y) • z - y), by
        simp only [map_neg, neg_mul, inv_of_ι_mul_ι_mul_ι Q z y]⟩
  ·
    simp only [Units.val_one, map_one, one_mul, inv_one, mul_one, LinearMap.mem_range,
      exists_apply_eq_apply, forall_const]
  · intro a b ha hb y
    simp only [Units.val_mul, map_mul, mul_inv_rev, LinearMap.mem_range]
    cases' hb y with c hc
    suffices ∃ y_1 : M, (ι Q) y_1 = involute ↑a * (involute ↑b * (ι Q) y * ↑b⁻¹) * ↑a⁻¹
      by
      cases' this with p hp
      refine' ⟨p, by simp only [hp, mul_assoc]⟩
    rw [← hc]
    exact ha c
#align mem_lipschitz_involute_le mem_lipschitz_involute_le

theorem coe_mem_lipschitz_iff_mem {x : (CliffordAlgebra Q)ˣ} :
    ↑x ∈ (lipschitz Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ↔ x ∈ lipschitz Q :=
  by
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply, exists_prop]
  norm_cast
  exact exists_eq_right
#align coe_mem_lipschitz_iff_mem coe_mem_lipschitz_iff_mem

-- instance : Membership (CliffordAlgebra Q) (lipschitz Q) :=

/-- `pinGroup Q` is defined as the infimum of `lipschitz Q` and `unitary (clifford_algebra Q)`.
See `mem_iff`. -/
def pinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q) :=
  (lipschitz Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ⊓ unitary _
#align pin_group pinGroup

namespace pinGroup

/-- An element is in `pinGroup Q` if and only if it is in `lipschitz Q` and `unitary`. -/
theorem mem_iff {x : CliffordAlgebra Q} :
    x ∈ pinGroup Q ↔
      x ∈ (lipschitz Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ∧
        x ∈ unitary (CliffordAlgebra Q) :=
  Iff.rfl
#align pin_group.mem_iff pinGroup.mem_iff

theorem mem_lipschitz {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    x ∈ (lipschitz Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) :=
  hx.1
#align pin_group.mem_lipschitz pinGroup.mem_lipschitz

theorem mem_unitary {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    x ∈ unitary (CliffordAlgebra Q) :=
  hx.2
#align pin_group.mem_unitary pinGroup.mem_unitary

theorem units_mem_iff {x : (CliffordAlgebra Q)ˣ} :
    ↑x ∈ pinGroup Q ↔ x ∈ lipschitz Q ∧ ↑x ∈ unitary (CliffordAlgebra Q) := by
  rw [mem_iff, coe_mem_lipschitz_iff_mem]
#align pin_group.units_mem_iff pinGroup.units_mem_iff

theorem units_mem_lipschitz {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q) : x ∈ lipschitz Q :=
  (units_mem_iff.1 hx).1
#align pin_group.units_mem_lipschitz pinGroup.units_mem_lipschitz

-- /-- If x is in `pinGroup Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
-- statement presumably being true only in finite dimensions.-/
-- theorem units_mem_conjAct_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
--     [Invertible (2 : R)] : ConjAct.toConjAct x • (ι Q).range ≤ (ι Q).range :=
--   mem_lipschitz_conjAct_le (units_mem_lipschitz hx)
-- #align pin_group.units_mem_conj_act_le pinGroup.units_mem_conjAct_le

-- /-- This is another version of `units_mem_conj_act_le` which uses `involute`. -/
-- theorem units_mem_involute_act_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
--     [Invertible (2 : R)] (y : M) : involute ↑x * ι Q y * ↑x⁻¹ ∈ (ι Q).range :=
--   mem_lipschitz_involute_le (units_mem_lipschitz hx) y
-- #align pin_group.units_mem_involute_act_le pinGroup.units_mem_involute_act_le

@[simp]
theorem star_hMul_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : star x * x = 1 :=
  hx.2.1
#align pin_group.star_mul_self_of_mem pinGroup.star_hMul_self_of_mem

@[simp]
theorem hMul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : x * star x = 1 :=
  hx.2.2
#align pin_group.mul_star_self_of_mem pinGroup.hMul_star_self_of_mem

/-- See `star_mem_iff` for both directions. -/
theorem star_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : star x ∈ pinGroup Q :=
  by
  rw [mem_iff] at hx ⊢
  refine' ⟨_, unitary.star_mem hx.2⟩
  rcases hx with ⟨⟨y, hy₁, hy₂⟩, hx₂, hx₃⟩
  simp only [Subgroup.coe_toSubmonoid, SetLike.mem_coe] at hy₁
  simp only [Units.coeHom_apply] at hy₂
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply, exists_prop]
  refine' ⟨star y, _, by simp only [hy₂, Units.coe_star]⟩
  rw [← hy₂] at hx₃
  have hy₃ : y * star y = 1 := by
    rw [← Units.eq_iff]
    simp only [hx₃, Units.val_mul, Units.coe_star, Units.val_one]
  apply_fun fun x => y⁻¹ * x at hy₃
  simp only [inv_mul_cancel_left, mul_one] at hy₃
  simp only [hy₃, hy₁, inv_mem_iff]
#align pin_group.star_mem pinGroup.star_mem

/-- An element is in `pinGroup Q` if and only if `star x` is in `pinGroup Q`.
See `star_mem` for only one direction. -/
@[simp]
theorem star_mem_iff {x : CliffordAlgebra Q} : star x ∈ pinGroup Q ↔ x ∈ pinGroup Q :=
  by
  refine' ⟨_, star_mem⟩
  intro hx
  convert star_mem hx
  exact (star_star x).symm
#align pin_group.star_mem_iff pinGroup.star_mem_iff

instance : Star (pinGroup Q) :=
  ⟨fun x => ⟨star x, star_mem x.prop⟩⟩

@[simp, norm_cast]
theorem coe_star {x : pinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl
#align pin_group.coe_star pinGroup.coe_star

theorem coe_star_hMul_self (x : pinGroup Q) : (star x : CliffordAlgebra Q) * x = 1 :=
  star_hMul_self_of_mem x.prop
#align pin_group.coe_star_mul_self pinGroup.coe_star_hMul_self

theorem coe_hMul_star_self (x : pinGroup Q) : (x : CliffordAlgebra Q) * star x = 1 :=
  hMul_star_self_of_mem x.prop
#align pin_group.coe_mul_star_self pinGroup.coe_hMul_star_self

@[simp]
theorem star_hMul_self (x : pinGroup Q) : star x * x = 1 :=
  Subtype.ext <| coe_star_hMul_self x
#align pin_group.star_mul_self pinGroup.star_hMul_self

@[simp]
theorem hMul_star_self (x : pinGroup Q) : x * star x = 1 :=
  Subtype.ext <| coe_hMul_star_self x
#align pin_group.mul_star_self pinGroup.hMul_star_self

/-- `pinGroup Q` forms a group where the inverse is `star`. -/
instance : Group (pinGroup Q) :=
  { Submonoid.toMonoid _ with
    inv := star
    mul_left_inv := star_hMul_self }

-- set_option trace.Meta.synthInstance true in
set_option synthInstance.maxHeartbeats 25000 in
instance : InvolutiveStar (pinGroup Q) :=
  ⟨fun _ => by
    ext; simp only [coe_star, star_star]
  ⟩

instance : StarMul (pinGroup Q) :=
  ⟨fun _ _ => by ext; simp only [coe_star, Submonoid.coe_mul, star_mul]⟩

instance : Inhabited (pinGroup Q) :=
  ⟨1⟩

theorem star_eq_inv (x : pinGroup Q) : star x = x⁻¹ :=
  rfl
#align pin_group.star_eq_inv pinGroup.star_eq_inv

theorem star_eq_inv' : (star : pinGroup Q → pinGroup Q) = Inv.inv :=
  rfl
#align pin_group.star_eq_inv' pinGroup.star_eq_inv'

/-- The elements in `pinGroup Q` embed into (clifford_algebra Q)ˣ. -/
@[simps]
def toUnits : pinGroup Q →* (CliffordAlgebra Q)ˣ
    where
  toFun x := ⟨x, ↑x⁻¹, coe_hMul_star_self x, coe_star_hMul_self x⟩
  map_one' := Units.ext rfl
  map_mul' x y := Units.ext rfl
#align pin_group.to_units pinGroup.toUnits

theorem toUnits_injective : Function.Injective (toUnits : pinGroup Q → (CliffordAlgebra Q)ˣ) :=
  fun x y h => Subtype.ext <| Units.ext_iff.mp h
#align pin_group.to_units_injective pinGroup.toUnits_injective

end pinGroup

end Pin

section Spin

open CliffordAlgebra MulAction

open scoped Pointwise

/-- `spinGroup Q` is defined as the infimum of `pinGroup Q` and `clifford_algebra.even Q`.
See `mem_iff`. -/
def spinGroup (Q : QuadraticForm R M) :=
  pinGroup Q ⊓ (CliffordAlgebra.even Q).toSubring.toSubmonoid
#align spin_group spinGroup

namespace spinGroup

/-- An element is in `spinGroup Q` if and only if it is in `pinGroup Q` and `even Q`. -/
theorem mem_iff {x : CliffordAlgebra Q} : x ∈ spinGroup Q ↔ x ∈ pinGroup Q ∧ x ∈ even Q :=
  Iff.rfl
#align spin_group.mem_iff spinGroup.mem_iff

theorem mem_pin {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x ∈ pinGroup Q :=
  hx.1
#align spin_group.mem_pin spinGroup.mem_pin

theorem mem_even {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x ∈ even Q :=
  hx.2
#align spin_group.mem_even spinGroup.mem_even

theorem units_mem_lipschitz {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q) : x ∈ lipschitz Q :=
  pinGroup.units_mem_lipschitz (mem_pin hx)
#align spin_group.units_mem_lipschitz spinGroup.units_mem_lipschitz

/-- If x is in `spinGroup Q`, then `involute x` is equal to x.-/
theorem mem_involute_eq {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : involute x = x :=
  involute_eq_of_mem_even (mem_even hx)
#align spin_group.mem_involute_eq spinGroup.mem_involute_eq

theorem units_involute_act_eq_conjAct {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
    [Invertible (2 : R)] (y : M) : involute ↑x * ι Q y * ↑x⁻¹ = ConjAct.toConjAct x • (ι Q y) := by
      rw [mem_involute_eq hx, @ConjAct.units_smul_def, @ConjAct.ofConjAct_toConjAct]
#align spin_group.units_involute_act_eq_conj_act spinGroup.units_involute_act_eq_conjAct

/- If x is in `spinGroup Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions.-/
-- theorem units_mem_conjAct_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
--     [Invertible (2 : R)] : ConjAct.toConjAct x • (ι Q).range ≤ (ι Q).range :=
--   mem_lipschitz_conjAct_le (units_mem_lipschitz hx)
-- #align spin_group.units_mem_conj_act_le spinGroup.units_mem_conjAct_le

/- This is another version of `units_mem_conj_act_le` which uses `involute`.-/
-- theorem units_mem_involute_act_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
--     [Invertible (2 : R)] (y : M) : involute ↑x * ι Q y * ↑x⁻¹ ∈ (ι Q).range :=
--   mem_lipschitz_involute_le (units_mem_lipschitz hx) y
-- #align spin_group.units_mem_involute_act_le spinGroup.units_mem_involute_act_le

@[simp]
theorem star_hMul_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : star x * x = 1 :=
  hx.1.2.1
#align spin_group.star_mul_self_of_mem spinGroup.star_hMul_self_of_mem

@[simp]
theorem hMul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x * star x = 1 :=
  hx.1.2.2
#align spin_group.mul_star_self_of_mem spinGroup.hMul_star_self_of_mem

/-- See `star_mem_iff` for both directions. -/
theorem star_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : star x ∈ spinGroup Q :=
  by
  rw [mem_iff] at hx ⊢
  cases' hx with hx₁ hx₂
  refine' ⟨pinGroup.star_mem hx₁, _⟩
  dsimp only [CliffordAlgebra.even] at hx₂ ⊢
  simp only [Submodule.mem_toSubalgebra] at hx₂ ⊢
  simp only [star_def, reverse_mem_evenOdd_iff, involute_mem_evenOdd_iff, hx₂]
#align spin_group.star_mem spinGroup.star_mem

/-- An element is in `spinGroup Q` if and only if `star x` is in `spinGroup Q`.
See `star_mem` for only one direction.
-/
@[simp]
theorem star_mem_iff {x : CliffordAlgebra Q} : star x ∈ spinGroup Q ↔ x ∈ spinGroup Q :=
  by
  refine' ⟨_, star_mem⟩
  intro hx
  convert star_mem hx
  exact (star_star x).symm
#align spin_group.star_mem_iff spinGroup.star_mem_iff

instance : Star (spinGroup Q) :=
  ⟨fun x => ⟨star x, star_mem x.prop⟩⟩

@[simp, norm_cast]
theorem coe_star {x : spinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl
#align spin_group.coe_star spinGroup.coe_star

theorem coe_star_hMul_self (x : spinGroup Q) : (star x : CliffordAlgebra Q) * x = 1 :=
  star_hMul_self_of_mem x.prop
#align spin_group.coe_star_mul_self spinGroup.coe_star_hMul_self

theorem coe_hMul_star_self (x : spinGroup Q) : (x : CliffordAlgebra Q) * star x = 1 :=
  hMul_star_self_of_mem x.prop
#align spin_group.coe_mul_star_self spinGroup.coe_hMul_star_self

@[simp]
theorem star_hMul_self (x : spinGroup Q) : star x * x = 1 :=
  Subtype.ext <| coe_star_hMul_self x
#align spin_group.star_mul_self spinGroup.star_hMul_self

@[simp]
theorem hMul_star_self (x : spinGroup Q) : x * star x = 1 :=
  Subtype.ext <| coe_hMul_star_self x
#align spin_group.mul_star_self spinGroup.hMul_star_self

/-- `spinGroup Q` forms a group where the inverse is `star`. -/
instance : Group (spinGroup Q) :=
  { Submonoid.toMonoid _ with
    inv := star
    mul_left_inv := star_hMul_self }

set_option synthInstance.maxHeartbeats 25000 in
instance : InvolutiveStar (spinGroup Q) :=
  ⟨fun _ => by ext; simp only [coe_star, star_star]⟩

instance : StarMul (spinGroup Q) :=
  ⟨fun _ _ => by ext; simp only [coe_star, Submonoid.coe_mul, star_mul]⟩

instance : Inhabited (spinGroup Q) :=
  ⟨1⟩

theorem star_eq_inv (x : spinGroup Q) : star x = x⁻¹ :=
  rfl
#align spin_group.star_eq_inv spinGroup.star_eq_inv

theorem star_eq_inv' : (star : spinGroup Q → spinGroup Q) = Inv.inv :=
  rfl
#align spin_group.star_eq_inv' spinGroup.star_eq_inv'

/-- The elements in `spinGroup Q` embed into (clifford_algebra Q)ˣ. -/
@[simps]
def toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ
    where
  toFun x := ⟨x, ↑x⁻¹, coe_hMul_star_self x, coe_star_hMul_self x⟩
  map_one' := Units.ext rfl
  map_mul' x y := Units.ext rfl
#align spin_group.to_units spinGroup.toUnits

theorem toUnits_injective : Function.Injective (toUnits : spinGroup Q → (CliffordAlgebra Q)ˣ) :=
  fun x y h => Subtype.ext <| Units.ext_iff.mp h
#align spin_group.to_units_injective spinGroup.toUnits_injective

end spinGroup

end Spin
