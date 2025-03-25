import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.GroupTheory.SpecificGroups.Quaternion
-- import Mathlib.GroupTheory.Subgroup.Actions
-- import Mathlib.GroupTheory.Subgroup.Basic
-- import Mathlib.GroupTheory.Subgroup.Finite
-- import Mathlib.GroupTheory.Subgroup.MulOpposite
-- import Mathlib.GroupTheory.Subgroup.Pointwise
-- import Mathlib.GroupTheory.Subgroup.Saturated
-- import Mathlib.GroupTheory.Subgroup.Simple
-- import Mathlib.GroupTheory.Subgroup.ZPowers
import Mathlib.RepresentationTheory.Basic
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.DomAct.Basic
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Invertible
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
-- import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Logic.Equiv.Defs
-- import Mathlib.Data.ZMod.Module
import Mathlib.GroupTheory.PresentedGroup
-- import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Tactic

-- Inspired by Finite symmetric groups in Physics
-- Following Representations and Characters of Groups

#check Representation.trivial

#check Module.End

#check DistribMulAction.toModuleEnd

#check CategoryTheory.End

#check CategoryTheory.Aut

#check Action.ρAut

#check Fact

#check IsCyclic.exists_generator

#check isCyclic_of_prime_card

variable (p : ℕ) [Fact p.Prime] (F : Type uF) [Field F] (ι : Type uι) [Finite ι] [LT ι] (R : Type uR) [Ring R] -- (fp : ι → F)

-- a list of indices, sorted
abbrev Model.Index := {l : List ι // l.Sorted (· < ·) }

def fp := Model.Index ι →₀ F

def ee (g : fp F ι) : fp F ι := g

#check Fin p

-- def Fp : Fin p → F := sorry

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Action.20of.20permutations.20on.20functions.2E

instance : MulAction (Equiv.Perm β)ᵐᵒᵖ β := sorry

variable (α β : Type*) in
#synth MulAction ((Equiv.Perm α)ᵐᵒᵖ)ᵈᵐᵃ (α → β) -- works


-- variable (α β : Type*) in
-- #synth MulAction ((Equiv.Perm α)ᵈᵐᵃ)ᵐᵒᵖ (α → β) -- fails

#minimize_imports

#check Group

#check Semigroup.mul_assoc

#check MulOneClass.one_mul

#check MulOneClass.mul_one

#check Group.inv_mul_cancel

#check Subgroup

variable {G H : Type uG} [Group G] [Group H] (K L : Subgroup G)

#check Subgroup G

#check G × H

#check Prod.instGroup

#check Group.FG

#check MulHom

#check MonoidHom

#check Action.Hom

#check Representation.asGroupHom

#check Subgroup.Normal

#check Subgroup.index

#check HasQuotient.Quotient G K

/-
failed to synthesize instance
  HDiv (Type uG) (Subgroup G) ?m.4221
-/
-- #check G / K

#check IsSimpleGroup

#check QuotientGroup.instHasQuotientSubgroup

#check QuotientGroup.Quotient.group

#check LinearMap.ker

#check Set.preimage_kernImage

#check Setoid.ker

#check Filter.ker

#check MonoidHom.ker

#check RingHom.ker

#check MonoidHom.range

#check QuotientGroup.quotientKerEquivRange

#check QuotientGroup.quotientInfEquivProdNormalQuotient

#check QuotientGroup.quotientQuotientEquivQuotient

#check Basis

#check Module.Finite.of_basis

#check Module.Free

#check Module.Finite.finite_basis

#check Basis.ofVectorSpace

#check Module.finBasis

#check Basis.ofVectorSpaceIndex

/- The `Subgroup` generated by a set. -/
-- def closure (k : Set G) : Subgroup G :=
--   sInf { K | k ⊆ K }
#check Subgroup.closure

/- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
-- def span (s : Set M) : Submodule R M :=
--   sInf { p | s ⊆ p }
#check Submodule.span

#check Submodule R (ι →₀ R)

#synth Module R (ι →₀ R)

/- Interprets (l : α →₀ R) as linear combination of the elements in the family (v : α → M) and
    evaluates this linear combination. -/
-- protected def total : (α →₀ R) →ₗ[R] M :=
--   Finsupp.lsum ℕ fun i => LinearMap.id.smulRight (v i)
#check Finsupp.linearCombination 

/- `LinearIndependent R v` states the family of vectors `v` is linearly independent over `R`. -/
-- def LinearIndependent : Prop :=
--   LinearMap.ker (Finsupp.total ι M R v) = ⊥
#check LinearIndependent

#check Module.rank

#check Module.Free.chooseBasis

#check Basis.coord

#check Basis.exists_basis

#check DirectSum

#check Module.Free.directSum

#check DirectSum.instAlgebra

#check DirectSum.add_apply

#check LinearMap

#check LinearMap.ker

#check LinearMap.range

#check LinearMap.rank_range_add_rank_ker

#check LinearEquiv

#check Basis.map

#check LinearEquiv.ofRankEq

#check Module.End

#check Module.End.semiring

-- TODO: PR?
-- #check Module.End.algebra
#check Module.End.instAlgebra

#check DistribMulAction.toLinearMap

#check DistribMulAction.toModuleEnd

#check LinearMap.toMatrix

#check linearMap_toMatrix_mul_basis_toMatrix

#check Matrix

section

variable (l m n: Type u) (α : Type uα) [Fintype l] [Fintype m] [Fintype n] [Mul α] [AddCommMonoid α] (x : Matrix l m α) (y : Matrix m n α) (z : Matrix l n α)

#check x * y

#synth HMul (Matrix l m α) (Matrix m n α) (Matrix l n α)

end

#check Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

#check Matrix.mul_apply

#check Matrix.sum_apply

#check Matrix.toLin

#check Matrix.Represents

#check Matrix.isRepresentation

#check Matrix.isRepresentation.toEnd

#check PiToModule.fromMatrix

#check Matrix.inv

#check Matrix.invOf_eq

#check Matrix.invOf_eq_nonsing_inv

#check Matrix.invertibleOfDetInvertible

-- TODO: an endomorphism is invertible iff the matrix is invertible

#check algEquivMatrix

-- change of basis matrix
#check basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix

#check Module.End.eigenspace

#check Module.End.HasEigenvalue

#check Module.End.HasEigenvector

#check Module.End.Eigenvalues

/- The generalized eigenspace for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
kernel of `(f - μ • id) ^ k`. (Def 8.10 of [axler2015]). Furthermore, a generalized eigenspace for
some exponent `k` is contained in the generalized eigenspace for exponents larger than `k`. -/
-- def generalizedEigenspace (f : End R M) (μ : R) : ℕ →o Submodule R M where
--   toFun k := LinearMap.ker ((f - algebraMap R (End R M) μ) ^ k)
--   monotone' k m hm := by
--     simp only [← pow_sub_mul_pow _ hm]
--     exact
--       LinearMap.ker_le_ker_comp ((f - algebraMap R (End R M) μ) ^ k)
--         ((f - algebraMap R (End R M) μ) ^ (m - k))
#check Module.End.genEigenspace

#check OrderHom

#check Module.End.eigenspaces_independent

#check Module.End.eigenvectors_linearIndependent

#check Module.End.exists_eigenvalue

#check Matrix.IsHermitian.det_eq_prod_eigenvalues

#check Basis.det

#check LinearMap.det

#check Subgroup.zpowers

#check IsFreeGroup.Generators

#check Matrix.diag

#check Matrix.diagonal

#check LinearMap.IsProj

#check LinearMap.isProj_iff_idempotent

-- TODO: л is projection of a vector space V. Then V = Im л 0 Ker л.

#check Submodule.prod

#check LinearMap.coprod

#check Matrix.GeneralLinearGroup

#check Matrix.ext

#check Representation

#check Representation.asGroupHom

#check Representation.asAlgebraHom

#check Representation.asModuleEquiv

#check Representation.ofMulAction

#check Representation.ofDistribMulAction

#check Representation.linHom

#find_home QuadraticMap.isometryEquivBasisRepr

-- section

-- variable {k G V: Type*}  [CommRing k] [Monoid G] [AddCommMonoid V] [Module k V]

-- variable (n : Type uN) [DecidableEq n] [Fintype n]

-- variable (ρ₁ ρ₂ : Representation k G V) (T' : Matrix.GeneralLinearGroup n k)

-- #check T'⁻¹

-- #check Matrix.GeneralLinearGroup.toLin T'

-- def Representation.equivalent : Prop :=
--   ∃ T : Matrix.GeneralLinearGroup n k,
--     ∀ g, ρ₁ g = T⁻¹ ∘ₗ ρ₂ g ∘ₗ T
-- end

#check Representation.trivial

#check CategoryTheory.Functor.Faithful.of_iso


-- #check Real.cos -1

-- #check Real.cos (-1 : ℝ)

-- #check Complex.cos (-1 : ℂ)

-- example : Real.sqrt 1 = 1 := by
--   norm_num

-- example : Real.sqrt 1 = 1 ^ (1 / 2 : ℝ) := by
--   norm_num
--   done

-- example : (Real.sqrt 2)^2 = (2 : ℝ) := by
--   norm_num
--   done -- works

-- example : Real.sqrt 2 = 2 ^ (1 / 2) → false := by
--   norm_num
--   done -- works

-- example : Real.sqrt 2 = 2 ^ (1 / 2 : ℝ) := by
--   norm_num
--   done -- fails

-- example : Real.sqrt 2 = 2 ^ (1 / 2 : ℚ) := by
--   norm_num

--   done

-- example : Real.sqrt (-1 : ℝ ) = Real.sqrt (-4 : ℝ ) := by
--   norm_num
--   done

-- example : (2 : ℝ) * Real.sqrt (-1 : ℝ ) = Real.sqrt (-4 : ℝ ) := by
--   norm_num
--   done

-- TODO: FG-module

-- TODO: permutation module


#check MonoidAlgebra

#check LinearMap.trace

#check LinearMap.trace_eq_matrix_trace

#check LinearMap.trace_eq_contract

#check LinearMap.baseChange

#check LinearMap.trace_eq_contract_of_basis

#check alternatingGroup (Fin 8)

variable (n : ℕ)
abbrev Aₙ : Matrix (Fin n) (Fin n) ℕ := Matrix.of fun i j : Fin n =>
    if i == j then 1
      else (if i == n - 1 ∨ j == n - 1 then 2 else 3)

#check Aₙ 8

#check QuaternionGroup 8

-- https://en.wikipedia.org/wiki/Quaternion_group
-- https://kconrad.math.uconn.edu/blurbs/grouptheory/genquat.pdf
-- https://math.stackexchange.com/questions/305455/generalized-quaternion-group
abbrev Q₈ := QuaternionGroup 2

abbrev C₃ := Multiplicative (ZMod 3)

-- variable (z : Z₃)

-- #synth Group Z₃

-- variable {C₃ : Type} [Group C₃] [Fintype C₃] (h : Fintype.card C₃ = 3) [IsCyclic C₃]

-- #check C₃

#synth CommRing <| ZMod 3

#synth AddGroup <| ZMod 3

#check Multiplicative.group

#synth CommGroup <| Multiplicative (ZMod 3)

#synth IsCyclic C₃

#eval Fintype.card C₃

-- #eval orderOf C₃

#check Additive.ofMul <| Multiplicative (ZMod 3)

#check Multiplicative.toAdd <| Multiplicative <| ZMod 3

-- #synth AddGroup <| Multiplicative.toAdd <| Multiplicative <| ZMod 3

#synth IsCyclic C₃

#synth Group Q₈

#check MulAut.conj

#check RingEquiv

#check SMul

#check MulAction

#check DistribMulAction

#check LinearPMap

#check LinearPMap.instMulAction

-- #check ​Equiv.Perm

-- instance : MulAction C₃ Q₈ where
--   smul g h :=

def c1 : C₃ := 1

#eval c1.val

def f (n : ℕ) : ZMod 3 := n % 3

#eval f 0

#eval f 1

#eval f 2

/-
0
-/
#eval f 3

#eval f 2 |>.val

/-
8
-/
#eval Fintype.card Q₈

-- TODO: typo Multiplication of the dihedral group PR

def e : Q₈ := QuaternionGroup.a 0

def i : Q₈ := QuaternionGroup.a 1

def ne : Q₈ := QuaternionGroup.a 2

def ni : Q₈ := QuaternionGroup.a 3

def j : Q₈ := QuaternionGroup.xa 0

def nk : Q₈ := QuaternionGroup.xa 1

def nj : Q₈ := QuaternionGroup.xa 2

def k : Q₈ := QuaternionGroup.xa 3

def QuaternionGroup.f : Q₈ → Q₈
  | a 1 => xa 0   -- i -> j
  | xa 0 => xa 3  -- j -> k
  | xa 3 => a 1   -- k -> i
  | a 3 => xa 2   -- ni -> nj
  | xa 2 => xa 1  -- nj -> nk
  | xa 1 => a 3   -- nk -> ni
  | x => x        -- e, ne

#check ZMod.card

-- example (z : ZMod 3) : 1 = 1 := by
--   cases z.val with
--   | zero => rfl
--   | succ n => rfl

-- example (q : Q₈) : Nat.repeat QuaternionGroup.f 3 q = 1 := by
--   simp only [QuaternionGroup.one_def, Nat.repeat]
--   cases q with
--   | a i => cases i.val with
--     | zero =>
--         rw (config := {occs := .pos {1} }) [QuaternionGroup.f]
--         done
--     | succ n => repeat { rw [QuaternionGroup.f] }
--     | _ => sorry
--   | _ => sorry
--   done

-- def φ : C₃ →* MulAut Q₈ where
--   toFun c := {
--       toFun := fun q => Nat.repeat QuaternionGroup.f c.val q, -- ^c.val,
--       invFun := fun q => Nat.repeat QuaternionGroup.f (c.val + 1) q, --^c.val,
--       left_inv := fun x => by
--         simp [Function.LeftInverse, QuaternionGroup.f]
--         done
--       right_inv := fun x => by simp [Function.RightInverse]
--       map_mul' := by simp [Function.LeftInverse, Function.RightInverse]
--   }
--   map_one' := sorry
--   map_mul' := sorry

-- #check Q₈ ⋊[φ] C₃

-- #check Q₈ ⋊[φ] C₃

-- https://en.wikipedia.org/wiki/Presentation_of_a_group
-- https://mathworld.wolfram.com/GroupPresentation.html
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Coxeter.20Groups
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Group.20algebra.20over.20finite.20groups
-- https://encyclopediaofmath.org/wiki/Schur_index
-- https://en.wikipedia.org/wiki/Covering_groups_of_the_alternating_and_symmetric_groups
-- https://math.stackexchange.com/questions/4242277/number-of-schur-covering-groups
-- https://en.m.wikipedia.org/wiki/Tietze_transformations
-- https://mathworld.wolfram.com/GroupAlgebra.html
-- https://github.com/leanprover-community/mathlib4/commits/j-loreaux/generator/
#check PresentedGroup

variable {B : Type*} [DecidableEq B] in
def demo := PresentedGroup <| Set.range <| Function.uncurry fun (i j : B) => FreeGroup.of i * FreeGroup.of j

inductive generator (n : ℕ)
  | a : ZMod n → generator n
  | b : ZMod n → generator n
  deriving DecidableEq

def rel : generator n → generator n → FreeGroup (generator n)
  | generator.a i, generator.a j => FreeGroup.of (generator.a i) * FreeGroup.of (generator.a j)
  | generator.b i, generator.b j => FreeGroup.of (generator.b i) * FreeGroup.of (generator.b j)
  | generator.a i, generator.b j => (FreeGroup.of (generator.a j) * FreeGroup.of (generator.b i))^n
  | generator.b i, generator.a j => (FreeGroup.of (generator.b j) * FreeGroup.of (generator.a i))^n

#check rel

/-- The presentation of the Dihedral group which makes it a Coxeter group is
⟨a, b | a^2 = 1, b^2 = 1, (a * b)^n = 1⟩ -/
def DihedralPresentedGroup {_i : ZMod n} := PresentedGroup <| Set.range <| Function.uncurry <| rel n

namespace DihedralPresentedGroup

inductive pre (n : ℕ)
  | a : ZMod n → pre n
  | b : ZMod n → pre n
  deriving DecidableEq

#check (1 : FreeGroup (pre n))

/-- The presentation of the Dihedral group which makes it a Coxeter group is
⟨a, b | a^2 = 1, b^2 = 1, (a * b)^n = 1⟩ -/
def rel {i : ZMod n} : Set (FreeGroup (pre n)) :=
  {FreeGroup.of (pre.a i)^2} ∪
  {FreeGroup.of (pre.b i)^2} ∪
  {(FreeGroup.of (pre.a i) * FreeGroup.of (pre.b i)) ^ n}

abbrev DihedralPresentedGroup' {i : ZMod n} := PresentedGroup <| @rel n i

end DihedralPresentedGroup

namespace PresentedQuaternionGroup

-- variable {X : Type*} [DecidableEq X]

inductive pre
  | x : pre
  | y : pre
  deriving DecidableEq

inductive rel {n : ℕ} : FreeGroup pre → FreeGroup pre → Prop
| cond1 : rel ((FreeGroup.of pre.x)^n) ((FreeGroup.of pre.y)^2)
| cond2 : rel ((FreeGroup.of pre.y)⁻¹ * (FreeGroup.of pre.x) * (FreeGroup.of pre.y)) ((FreeGroup.of pre.x)⁻¹)

end PresentedQuaternionGroup

namespace C

-- variable {X : Type*} [DecidableEq X]

inductive pre
  | a : pre
  deriving DecidableEq

def rel := {a : FreeGroup pre| a^n = 1}

end C

abbrev C (n : ℕ) := PresentedGroup <| C.rel n

#synth Group <| C 3

namespace D

inductive pre
  | x : pre
  | y : pre
  deriving DecidableEq

def x := FreeGroup.of pre.x
def y := FreeGroup.of pre.y

def rel : Set (FreeGroup pre) := {x^n} ∪ {y^2} ∪ {(x * y)^2}

end D

abbrev D (n : ℕ) := PresentedGroup <| D.rel n

namespace De

variable {X : Type*} [DecidableEq X]

def rel {x y : FreeGroup X} : Set (FreeGroup X) := {x^n} ∪ {y^2} ∪ {(x * y)^2}

end De

def De (n : ℕ) := PresentedGroup <| @De.rel n D.pre D.x D.y

namespace Q

inductive pre
  | x : pre
  | y : pre
  deriving DecidableEq

def x := FreeGroup.of pre.x
def y := FreeGroup.of pre.y

def rel : Set (FreeGroup pre) := {x^4} ∪ {y^4} ∪ {y⁻¹ * x * y * x}

end Q

abbrev Q := PresentedGroup <| Q.rel

#synth Group <| Q

def φ : C 3 →* MulAut Q where
  toFun c := {
      toFun := fun q => sorry,
      invFun := fun q => sorry,
      left_inv := fun x => by simp [Function.LeftInverse]; sorry
      right_inv := fun x => by simp [Function.RightInverse]; sorry
      map_mul' := by simp [Function.LeftInverse, Function.RightInverse]; sorry
  }
  map_one' := sorry
  map_mul' := sorry

#check Q ⋊[φ] C 3

#synth Group <| Q ⋊[φ] C 3

namespace BT

inductive pre
  | e : pre
  | ne : pre
  | i : pre
  | j : pre
  | k : pre
  | f : pre
  | g : pre
  deriving DecidableEq

def e := FreeGroup.of pre.e
def ne := FreeGroup.of pre.ne
def i := FreeGroup.of pre.i
def j := FreeGroup.of pre.j
def k := FreeGroup.of pre.k
def f := FreeGroup.of pre.f
def g := FreeGroup.of pre.g

def rel : Set (FreeGroup pre) :=
  {e} ∪ {ne^2} ∪ {i^4} ∪ {j^4} ∪ {i * j * k} ∪
  {f^3} ∪ {g^3} ∪ {f * g} ∪ {f⁻¹ * i * f * j⁻¹} ∪ {f⁻¹ * j * f * k⁻¹}

end BT

-- example (a b: BT) [Group BT] : a^6 = 1 := by
--   done

abbrev BT := PresentedGroup <| BT.rel

-- namespace TT

-- inductive pre
-- | ofQ :  FreeGroup Q.pre → pre
-- | ofC :  FreeGroup C.pre → pre

-- def relQ := { FreeGroup.of <| pre.ofQ q | q ∈ Q.rel }
-- def relC := { FreeGroup.of <| pre.ofC c | c ∈ C.rel 3 }

-- def QC := FreeGroup <| Q.pre × C.pre

-- def rel : Set (FreeGroup pre) :=
--   relQ ∪ relC

-- end TT

-- https://people.maths.bris.ac.uk/~matyd/GroupNames/1/e5/C3byQ8.html#s1
-- https://people.maths.bris.ac.uk/~matyd/GroupNames/1/SL(2,3).html
-- https://en.wikipedia.org/wiki/Direct_product_of_groups#Presentations
abbrev TT := Q × C 3

#synth Group <| TT

#check Prod

#check Prod.instGroup

#check MulHom

-- free product of groups
#check Monoid.Coprod

open Monoid.Coprod

#check Q ∗ C 3

namespace BT

def of := @PresentedGroup.of pre rel

def k' := BT.of pre.k
def f' := BT.of pre.f
def i' := BT.of pre.i

-- example : f'⁻¹ * k' * f' = i' := by
--   simp [f', k', i', BT.of, BT.rel] --, pre.k, pre.f, pre.i]
--   have h : i'^4 = BT.of pre.e := by
--     simp [i', BT.of, BT.rel]
--     done
--     done
--   done
--   done
--   done
--   done

end BT

-- TODO Tietze transformations
-- https://math.stackexchange.com/questions/4273898/proving-an-isomorphism-via-generators
