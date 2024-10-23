import Lake
open Lake DSL

package "sci-xp" where
  -- add package configuration options here

lean_lib «SciXp» where
  -- add library configuration options here

@[default_target]
lean_exe "sci-xp" where
  root := `Main
