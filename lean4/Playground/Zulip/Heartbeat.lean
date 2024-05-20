import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.Tactic

variable {R : Type*} [CommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

section Pin

open CliffordAlgebra MulAction

open scoped Pointwise

def lipschitz (Q : QuadraticForm R M) :=
  Subgroup.closure (Units.val ⁻¹' Set.range (ι Q) : Set (CliffordAlgebra Q)ˣ)

def pinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q) :=
  (lipschitz Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ⊓ unitary _

namespace pinGroup

theorem star_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : star x ∈ pinGroup Q := sorry

instance : Star (pinGroup Q) :=
  ⟨fun x => ⟨star x, star_mem x.prop⟩⟩

@[simp, norm_cast]
theorem coe_star {x : pinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl

set_option synthInstance.maxHeartbeats 20038 in
instance : InvolutiveStar (pinGroup Q) :=
  ⟨fun _ => by
    /-
    failed to synthesize

    (deterministic) timeout at 'typeclass', maximum number of heartbeats (20000) has been reached (use 'set_option synthInstance.maxHeartbeats <num>' to set the limit)
    -/
    ext; simp only [coe_star, star_star]
  ⟩

end pinGroup

end Pin
