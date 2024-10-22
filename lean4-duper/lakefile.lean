import Lake
open Lake DSL System

package «hello» {}

def leanVersion : String := s!"v{Lean.versionString}"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ leanVersion

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "v0.0.17"

@[default_target]
lean_lib DuperLand {
}

