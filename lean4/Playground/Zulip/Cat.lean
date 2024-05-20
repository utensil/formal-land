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

--This file should be redone following https://github.com/lftcm2023/lftcm2023/blob/master/LftCM/C10_Category_Theory/CategoryTheory.lean
