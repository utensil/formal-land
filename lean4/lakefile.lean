import Lake
open Lake DSL System

package «hello» {}

def leanVersion : String := s!"v{Lean.versionString}"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" -- @ leanVersion

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "main"

@[default_target]
lean_lib Playground {
--   -- srcDir := "Playground"
--   -- roots := #[`Hello, `LAMR, `Tactics]
}

@[test_runner]
lean_exe test where
  srcDir := "scripts"

lean_exe annotate where
  srcDir := "scripts"
