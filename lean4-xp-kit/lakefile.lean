import Lake
open Lake DSL

def leanVersion : String := s!"v{Lean.versionString}"

require "leanprover-community" / "batteries" @ git leanVersion

package "Lean4XpKit" where
  testDriver := "test"
  testDriverArgs := #["Lean4XpKit"]

@[default_target]
lean_lib «Lean4XpKit» where

lean_exe test where
  srcDir := "scripts"

lean_exe annotate where
  srcDir := "scripts"

