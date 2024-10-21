-- import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Tactic

open QuadraticForm BilinForm ExteriorAlgebra FiniteDimensional QuadraticMap

#check polar_self

universe uκ uR uM uι

variable {κ : Type uκ}
variable {R : Type uR} [CommRing R] [Invertible (2 : R)] [Nontrivial R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
-- variable {B : BilinForm R M}
variable (Q : QuadraticForm R M) {Cl : CliffordAlgebra Q} {Ex : ExteriorAlgebra R M}
variable [Module.Finite R M] [Module.Free R M]

variable {ι : Type uι}
variable [DecidableEq ι] [AddMonoid ι]
variable (𝒜 : ι → Submodule R (ExteriorAlgebra R M))

noncomputable def QuadraticForm.B := Classical.choose Q.exists_companion

#check Nat.sum_range_choose

#check Module.finrank_directSum

#check rank_directSum

#check DirectSum.decomposeAlgEquiv

#check ExteriorAlgebra.liftAlternatingEquiv

#check Module.Free

#check Module.Free.directSum

#check Module.rank

#check Q.B

#check CliffordAlgebra.equivExterior Q

#check Module.Free.multilinearMap

#check CliffordAlgebra.equivBaseChange

#check TensorAlgebra.rank_eq

#check TensorAlgebra.equivFreeAlgebra

#check TensorAlgebra.toExterior

#check ExteriorAlgebra.gradedAlgebra

#check ExteriorAlgebra.gradedAlgebra R M

-- example : Module.Free R (ExteriorAlgebra R M) := by

--   done

-- example : (∀ i, M [Λ^Fin i]→ₗ[R] M) = (∀ i, AlternatingMap R M M i) := by
--   done

example : Module.rank R M = Module.finrank R M := by
  exact (Module.finrank_eq_rank R M).symm

-- example : finrank R (TensorAlgebra R M) = 2^(finrank R M) := by

--   done

-- example : finrank R (CliffordAlgebra Q) = 2^(finrank R M) := by
--   -- let em := CliffordAlgebra.equivExterior Q
--   -- let Ex := em Cl
--   have h1 : finrank R (CliffordAlgebra Q) = finrank R (ExteriorAlgebra R M) := by
--     apply LinearEquiv.finrank_eq
--     exact CliffordAlgebra.equivExterior Q
--   have h2 : finrank R (ExteriorAlgebra R M) = finrank R (∀ i, M [Λ^Fin i]→ₗ[R] M) := by
--     apply LinearEquiv.finrank_eq
--     exact ExteriorAlgebra.liftAlternatingEquiv R M
--   have h3 : finrank R (ExteriorAlgebra R M) = 2^(finrank R M) := by

--     done
--   done

-- noncomputable def ExteriorAlgebra.equivFreeAlgebra (b : Basis κ R M) :
--     ExteriorAlgebra R M ≃ₐ[R] FreeAlgebra R κ := by
--   apply AlgEquiv.ofAlgHom
--   . apply ExteriorAlgebra.lift

--   done

--     -- (ExteriorAlgebra.lift _ (Finsupp.total _ _ _ (FreeAlgebra.ι _) ∘ₗ b.repr.toLinearMap))
--     -- (FreeAlgebra.lift _ (ι R ∘ b))
--     -- (by ext; simp)
--     -- (hom_ext <| b.ext <| fun i => by simp)

lemma rank_eq :
    Module.rank R (TensorAlgebra R M) = Cardinal.lift.{uR} (Cardinal.sum fun n ↦ Module.rank R M ^ n) := by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [(TensorAlgebra.equivFreeAlgebra b).toLinearEquiv.rank_eq, FreeAlgebra.rank_eq, Cardinal.mk_list_eq_sum_pow,
    Basis.mk_eq_rank'' b]

-- lemma rank_eq' :
--     Module.rank R (ExteriorAlgebra R M) = Cardinal.lift.{uR} (Cardinal.sum fun n ↦ Module.rank R M ^ n) := by
--   let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
--   rw [(ExteriorAlgebra.equivFreeAlgebra b).toLinearEquiv.rank_eq, FreeAlgebra.rank_eq, Cardinal.mk_list_eq_sum_pow,
--     Basis.mk_eq_rank'' b]
--   done

example : Module.rank R M = Module.rank R M := rfl

-- example : Module.rank R (CliffordAlgebra Q) = Module.rank R M := by

--   done

-- example (x y : M) : Q.B x y + Q.B y x = 2 * Q.B x y := by
--   have h1: Q (x + y) = Q x + Q y + Q.B x y := by
--       obtain ⟨b, hb⟩ := Q.exists_companion

--     done
--   have h2 : Q.B x y = Q (x + y) - Q x - Q y := by

--   have h : Q.B x y = Q.B y x := by

--     done
--   done
