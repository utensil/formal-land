import Lake
open Lake DSL System

package «Playground» where
  testDriver := "Lean4XpKit/test"
  testDriverArgs := #["Playground"]

def leanVersion : String := s!"v{Lean.versionString}"

require "Lean4XpKit" from ".." / "lean4-xp-kit"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ leanVersion -- last so Mathlib's transitive pins take precedence

@[default_target]
lean_lib Playground {
--   -- srcDir := "Playground"
--   -- roots := #[`Hello, `LAMR, `Tactics]
}


-- @[test_driver]
-- lean_exe test where
--   srcDir := "scripts"

-- lean_exe annotate where
--   srcDir := "scripts"
