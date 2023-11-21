import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

set_option pp.proofs.withType false

variable {R M} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)

abbrev ExteriorAlgebra.rMultivector (r : ℕ) : Submodule R (ExteriorAlgebra R M) :=
  (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] _) ^ r)

def ExteriorAlgebra.proj (mv : ExteriorAlgebra R M) (r : ℕ) : ExteriorAlgebra R M := 
  @GradedAlgebra.proj ℕ R (ExteriorAlgebra R M) _ _ _ _ _ ExteriorAlgebra.rMultivector _ r mv

namespace CliffordAlgebra

abbrev rMultivector (r : ℕ) : Submodule R (CliffordAlgebra Q) :=
  (ExteriorAlgebra.rMultivector r).comap (CliffordAlgebra.equivExterior Q)

abbrev ofGrade {r : ℕ} (mv : rMultivector Q r) : CliffordAlgebra Q := mv

variable {Q} in
def wedge (a b : CliffordAlgebra Q) : CliffordAlgebra Q :=
  (equivExterior Q).symm (equivExterior Q a * equivExterior Q b)

infix:65 " ⋏ " => wedge

variable (r : ℕ) (mv : CliffordAlgebra Q) in
#check equivExterior Q mv

def proj (mv : CliffordAlgebra Q) (i : ℕ) : CliffordAlgebra Q := (equivExterior Q).symm ((equivExterior Q mv).proj i)

#check proj

theorem wedge_mv_mem {ra rb} (a : rMultivector Q ra) (b : rMultivector Q rb) :
    a ⋏ b ∈ rMultivector Q (ra + rb) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [wedge, rMultivector, Submodule.mem_comap, LinearEquiv.apply_symm_apply] at *
  apply SetLike.mul_mem_graded <;> assumption

lemma outer_homo {i j} (u : rMultivector Q i) (v : rMultivector Q j) :
  u ⋏ v = proj Q (u * v) (i + j) := sorry

end CliffordAlgebra