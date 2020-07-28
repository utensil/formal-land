/-
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/mutual.20defs.3A.20ill-formed.20match.2Fequation.20expression/near/204543114
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/apply_instance.20for.20defs/near/205085382
-/
import algebra.category.Module.monoidal
import algebra.category.CommRing.basic

import tactic.delta_instance

open category_theory

variables {C : Type*} [category C] [monoidal_category C]

def tensor_power (X : C) : ℕ → C
| 0 := 𝟙_ C
| (n+1) := X ⊗ tensor_power n

example {R : CommRing} (M : Module R) : Module R := tensor_power M 17

-- And if you want to do this with unbundled objects:

universes u

variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]

-- @[derive [add_comm_group, module R]]
def foo : Type u :=
  (tensor_power (Module.of R M) 17 : Module R)

attribute [derive [add_comm_group, module R]] foo

-- WORKS
-- instance : add_comm_group (foo R M) := by { delta foo, apply_instance, }
-- instance : module R (foo R M) := by { delta foo, apply_instance, }

-- WORKS
-- instance : add_comm_group (foo R M) := by delta_instance foo
-- instance : module R (foo R M) :=  by delta_instance foo

-- namespace foo

-- /-
-- tactic.mk_instance failed to generate instance for
--   add_comm_group (foo R M)
-- -/
-- @[derive add_comm_group]
-- def to_add_comm_group := foo R M

-- /-
-- failed to synthesize type class instance for
-- R : Type u,
-- _inst_3 : comm_ring R,
-- M : Type u,
-- _inst_4 : add_comm_group M,
-- _inst_5 : module R M
-- ⊢ add_comm_group (to_module R M)
-- -/
-- @[derive module R]
-- def to_module := foo R M

-- end foo

