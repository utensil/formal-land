import DuperXp
-- import Mathlib.LinearAlgebra.Finrank
-- import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Tactic

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring

open QuadraticForm BilinForm ExteriorAlgebra FiniteDimensional

open Function
open BigOperators
open FiniteDimensional

universe uκ uR uM uι

variable {κ : Type uκ}
variable {R : Type uR} [CommRing R] [Invertible (2 : R)] [Nontrivial R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
-- variable {B : BilinForm R M}
variable (Q : QuadraticForm R M) {Cl : CliffordAlgebra Q} {Ex : ExteriorAlgebra R M}
variable [Module.Finite R M] [Module.Free R M]

set_option trace.duper.printProof true
set_option trace.duper.proofReconstruction true

theorem barber_paradox {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False :=
  by duper [*] {preprocessing := no_preprocessing, inhabitationReasoning := true}

example {G : Type} [hG : Group G] (x y : G) : x * y * y⁻¹ = x :=
  by duper? [inv_mul_cancel, one_mul, mul_assoc]

example (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  duper? [abs_le, abs_sub_abs_le_abs_sub]

/- Attempting to call `duper` directly on the original goal will fail because it isn't able to generate a
   counterexample to Surjf on its own. But if we provide the counterexample, `duper` can solve from there. -/
-- deterministic time out
-- example : ∀ f : α → Set α, ¬Surjective f := by
--   intro f Surjf
--   have counterexample := Surjf {i | i ∉ f i}
--   duper [Set.mem_setOf_eq, counterexample]

example : Module.rank R M = Module.finrank R M := by
  duper [Module.finrank_eq_rank]
  done
