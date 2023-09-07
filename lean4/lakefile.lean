import Lake
open Lake DSL System

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "d8c7d9897527e99b28862cdf5a4a13aefee95897"

package hello {}

@[default_target]
lean_lib Hello {
  srcDir := "examples"
  roots := #[`Hello, `LAMR, `Tactics]
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
        cmd := "lean"
        args := #[ex.path.toString]
        env := #[] -- #[("LEAN_PATH", searchPath)]
      })
    
      if r.exitCode == 0 then
        IO.println "  Success!🟢"
      else
        failed := failed.append #[(ex.path, r)]
        IO.println "  Failed!🔴"

  if failed.size != 0 then 
    IO.println "\nFailed examples:"
    for (ex, _) in failed do
      IO.println s!"  {ex}"
  
  let succeeded := total - failed.size
  let resultMarker := if succeeded == total then "✅" else "❌"

  IO.println s!"\nSuccessful examples: {succeeded} / {total} {resultMarker}"

  return 0