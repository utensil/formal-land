import Duper
import Mathlib.LinearAlgebra.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
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
  by duper? [mul_left_inv, one_mul, mul_assoc]

example (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  duper? [abs_le, abs_sub_abs_le_abs_sub]

/- Attempting to call `duper` directly on the original goal will fail because it isn't able to generate a
   counterexample to Surjf on its own. But if we provide the counterexample, `duper` can solve from there. -/
example : ∀ f : α → Set α, ¬Surjective f := by
  intro f Surjf
  have counterexample := Surjf {i | i ∉ f i}
  duper [Set.mem_setOf_eq, counterexample]

#check PreprocessingOption

example : Module.rank R M = finrank R M := by
  duper [finrank_eq_rank]
  done

example : finrank R (CliffordAlgebra Q) = finrank R (ExteriorAlgebra R M) := by
  exact LinearEquiv.finrank_eq <| CliffordAlgebra.equivExterior Q

example : finrank R (CliffordAlgebra Q) = finrank R (ExteriorAlgebra R M) := by
  duper [LinearEquiv.finrank_eq, CliffordAlgebra.equivExterior]
  done

-- example : finrank R (CliffordAlgebra Q) = finrank R (ExteriorAlgebra R M) := by
--   let clause_1_0 := eq_true «_exHyp_uniq.139473»;
--   let clause_3_0 := eq_true «_exHyp_uniq.139477»;
--   let clause_5_0 := fun a => (fun h => Duper.clausify_forall ((fun x_0 => x_0) a) h) clause_1_0;
--   let clause_6_0 := (fun h => of_eq_true h) (clause_5_0 «_exHyp_uniq.139432»);
--   let clause_7_0 := (fun h => Duper.clausify_not h) clause_3_0;
--   let clause_8_0 := (fun h => Duper.not_of_eq_false h) clause_7_0;
--   let clause_9_0 := (fun heq => (fun h => Eq.mp (congrArg (fun x => x ≠ e!_2) heq) h) clause_8_0) clause_6_0;
--   exact (fun h => (h rfl).elim) clause_9_0
--   done
