import Lake
open Lake DSL

def leanVersion : String := s!"v{Lean.versionString}"

require "leanprover-community" / "batteries" @ git leanVersion

package "Lean4XpKit" where

@[default_target]
lean_lib «Lean4XpKit» where
  -- add library configuration options here

lean_exe test where
  srcDir := "scripts"

lean_exe annotate where
  srcDir := "scripts"

