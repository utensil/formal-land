import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.NatIso

#check Quiver

universe u

variable {U: Type u} [Quiver U] (a b : U) in
#check a ⟶ b

#check CategoryTheory.isomorphismClasses

#check CategoryTheory.NatIso.pi

-- ≌
#check CategoryTheory.Equivalence
