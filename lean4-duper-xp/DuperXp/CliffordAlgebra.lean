import DuperXp
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

example : Module.finrank R (CliffordAlgebra Q) = Module.finrank R (ExteriorAlgebra R M) := by
  exact LinearEquiv.finrank_eq <| CliffordAlgebra.equivExterior Q

-- count_heartbeats in -- never ends

/-
(deterministic) timeout at `match`, maximum number of heartbeats (200000) has been reached
use `set_option maxHeartbeats <num>` to set the limit
use `set_option diagnostics true` to get diagnostic information
-/
-- example : finrank R (CliffordAlgebra Q) = finrank R (ExteriorAlgebra R M) := by
--   duper [LinearEquiv.finrank_eq, CliffordAlgebra.equivExterior]
--   done

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
