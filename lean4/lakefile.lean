import Lake
open Lake DSL System

package «hello» {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Hello» {
  -- srcDir := "examples"
  -- roots := #[`Hello, `LAMR, `Tactics]
}

-- lean_exe hello {
--   root := `Main
-- }

script check_examples (_args) do
  let cwd ← IO.currentDir

  let mut total := 0
  let mut failed : Array (FilePath × IO.Process.Output) := #[]

  for ex in (← (cwd / "examples").readDir) do
    if ex.path.extension == some "lean" then
      total := total + 1

      let r ← timeit s!"Running example: {ex.fileName}\t" (IO.Process.output {
        cmd := "lake"
        args := #["env", "lean", ex.path.toString]
        env := #[] -- #[("LEAN_PATH", searchPath)]
      })
    
      if r.exitCode == 0 then
        IO.println "  Success!🟢"
      else
        failed := failed.append #[(ex.path, r)]
        IO.println "  Failed!🔴"
        IO.println r.stdout
        IO.println r.stderr

  if failed.size != 0 then 
    IO.println "\nFailed examples:"
    for (ex, _) in failed do
      IO.println s!"  {ex}"
  
  let succeeded := total - failed.size
  let resultMarker := if succeeded == total then "✅" else "❌"

  IO.println s!"\nSuccessful examples: {succeeded} / {total} {resultMarker}"

  return 0