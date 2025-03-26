import Lake
open Lake DSL System

package «DuperXp» where 
  testDriver := "Lean4XpKit/test"
  testDriverArgs := #["DuperXp"]

-- def leanVersion : String := s!"v{Lean.versionString}"

-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4" @ leanVersion

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.16.0"

require "leanprover-community" / "batteries" @ git "v4.16.0" 

require Duper from git "https://github.com/leanprover-community/duper.git" @ "v0.0.23"

require "Lean4XpKit" from ".." / "lean4-xp-kit"

@[default_target]
lean_lib DuperXp where 

