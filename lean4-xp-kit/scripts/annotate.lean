/-
This is adapted from test.lean
-/
import Batteries.Data.String.Matcher
import Lean4XpKit.Utils
open IO.Process
open System



/--
Annotate Lean files.

If no arguments are provided, annotate everything in `Playground/` and `Playground/Zulip`.

If arguments are provided, they are interpreted as file names in `Playground/`, e.g.

- `lake exe annotate Hello` annotates `Playground/Hello.lean`
- `lake exe annotate Zulip/Agatha` annotates `Playground/Zulip/Agatha.lean`
-/
def main (args : List String) : IO Unit := do
  let cwd := mkFilePath ["."] -- ← IO.currentDir
  let LEAN4_XP_KIT_HOME := mkFilePath ["..", "lean4-xp-kit"]

  _ ← (← IO.Process.spawn { cmd := "lake", args := #["build"] }).wait
  -- Duper requires some additional time to build on first run.
  -- _ ← (← IO.Process.spawn { cmd := "lake", args := #["build", "Duper"] }).wait

  -- Collect test targets by walking `Playground/` and `Playground/Zulip`.
  -- let noNoisy := args.contains "--no-noisy"
  let verbose := args.contains "--verbose"
  let toc := args.contains "--toc"
  let enter : FilePath → IO Bool := fun path ↦ pure <| path.fileName != "NoCI"

  let positionalArgs := args.erase "--toc" |>.erase "--verbose"

  if positionalArgs.isEmpty then
    IO.eprintln "Usage: lake exe annotate [--verbose] [--toc] libraryName testFileName"
    exit 1

  let libraryName := positionalArgs.head!
  
  let targets <- match positionalArgs.drop 1 with
  | [] =>System.FilePath.walkDir (enter := enter) <| cwd / libraryName 
  | _ => pure <| (args.map fun t => mkFilePath [cwd.toString, libraryName, t] |>.withExtension "lean") |>.toArray
  let existing ← targets.filterM fun t => do pure <| (← t.pathExists) && !(← t.isDir) && (t.extension.getD "" == "lean")
  let tasks ← existing.mapM fun t => do
      IO.asTask do
        let format := if #["Hello.lean", "LAMR.lean"].contains <| t.fileName.getD "" then "rst" else "md"
        let ⟨elapsed, out⟩ ← time <| IO.Process.output {
            cmd :=  "bash",
            args := #[
              (LEAN4_XP_KIT_HOME / "annotate.sh").toString, t.toString, format]
          }
        let exitCode := out.exitCode
        if exitCode == 0 then
          if out.stdout.isEmpty && out.stderr.isEmpty then
            IO.println s!"✅ {t} {elapsed}"
          -- else if !out.stderr.isEmpty || out.stdout.containsSubstr "warning:" then
          --   IO.println s!"🟨 {t} {elapsed}"
          else
            IO.println s!"ℹ️  {t} {elapsed}"
        else
          IO.eprintln s!"❌ {t} {elapsed}"

        if verbose then
          unless out.stdout.isEmpty do IO.println out.stdout
          unless out.stderr.isEmpty do IO.eprintln out.stderr

        pure (exitCode, t, out)
  -- Wait on all the jobs and exit with 1 if any failed.
  let mut exitCode : UInt8 := 0
  let mut total := 0
  let mut succeeded := 0
  let mut jobs : Array (UInt32 × FilePath × IO.Process.Output) := #[]
  for t in tasks do
    let e ← IO.wait t
    total := total + 1
    match e with
    | .error f => IO.eprintln s!"❌ {f}"
    | .ok ⟨code, path, out⟩ =>
      jobs := jobs.push (code, path, out)
      if code == 0 then
        succeeded := succeeded + 1; pure ()

  if total - succeeded != 0 then
    exitCode := 1
    IO.println "\nFailed annotations:"
    for (code, t, out) in jobs do
      if code != 0 then
        IO.println s!"❌ {t}"
        unless out.stdout.isEmpty do IO.eprintln out.stdout
        unless out.stderr.isEmpty do IO.eprintln out.stderr
  let resultMarker := if succeeded == total then "✅" else "❌"
  IO.println s!"\nSuccessful annotations: {succeeded} / {total} {resultMarker}"

  if toc then
    for (code, t, _out) in jobs.insertionSort fun x y ↦ x.snd.fst.toString < y.snd.fst.toString do
      if code == 0 then
        let name := t.toString.replace "./Playground/" ""
        let url := t.withExtension "html" |>.toString.replace "./Playground/" "./"
        IO.println s!"- [{name}]({url})"
  exit exitCode
