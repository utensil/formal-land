import Lake
open Lake DSL System

package «hello» {}

def leanVersion : String := s!"v{Lean.versionString}"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" -- @ leanVersion

-- require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "main"

-- @[default_target]
-- lean_lib «Hello» {
--   -- srcDir := "examples"
--   -- roots := #[`Hello, `LAMR, `Tactics]
-- }

@[default_target]
lean_lib Playground {
}

@[test_runner]
lean_exe test where
  srcDir := "scripts"
