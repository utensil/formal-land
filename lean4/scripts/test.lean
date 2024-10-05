/-
This is adapted from https://github.com/leanprover-community/batteries/blob/078ac74e3157bd7b02628eca0260faa234878b2a/scripts/test.lean
with my own customizations on paths, options and summary output.
-/
import Batteries.Data.String.Matcher
import Playground.Utils
open IO.Process
open System

/--
Run tests.

If no arguments are provided, run everything in `Playground/` and `Playground/Zulip`.

If arguments are provided, they are interpreted as test names in `Playground/`, e.g.

- `lake exe test Hello` runs `Playground/Hello.lean`
- `lake exe test Zulip/Agatha` runs `Playground/Zulip/Agatha.lean`

Allow tests to produce output by default, use the flag `no-noisy` to disallow any output on stdout or stderr.
-/
def main (args : List String) : IO Unit := do
  let cwd := mkFilePath ["."] -- ← IO.currentDir

  -- We first run `lake build`, to ensure oleans are available.
  -- Alternatively, we could use `lake lean` below instead of `lake env lean`,
  -- but currently with parallelism this results in build jobs interfering with each other.
  _ ← (← IO.Process.spawn { cmd := "lake", args := #["build"] }).wait
  -- Duper requires some additional time to build on first run.
  -- _ ← (← IO.Process.spawn { cmd := "lake", args := #["build", "Duper"] }).wait

  -- Collect test targets by walking `Playground/` and `Playground/Zulip`.
  let noNoisy := args.contains "--no-noisy"
  let verbose := args.contains "--verbose"
  let enter : FilePath → IO Bool := fun path ↦ pure <| path.fileName != "NoCI" -- || true
  let targets <- match args.erase "--no-noisy" |>.erase "--verbose" with
  | [] =>System.FilePath.walkDir (enter := enter) <| cwd / "Playground"
  | _ => pure <| (args.map fun t => mkFilePath [cwd.toString, "Playground", t] |>.withExtension "lean") |>.toArray
  let existing ← targets.filterM fun t => do pure <| (← t.pathExists) && !(← t.isDir) && (t.extension.getD "" == "lean")
  let tasks ← existing.mapM fun t => do
      IO.asTask do
        let ⟨elapsed, out⟩ ← time <| IO.Process.output
          { cmd := "lake",
            args := #["env", "lean", t.toString],
            env := #[("LEAN_ABORT_ON_PANIC", "1")] }
        let mut exitCode := out.exitCode

        if exitCode == 0 then
          if out.stdout.isEmpty && out.stderr.isEmpty then
            IO.println s!"✅ {t} {elapsed}"
          else if !out.stderr.isEmpty || out.stdout.containsSubstr "warning:" then
            IO.println s!"🟨 {t} {elapsed}"
            unless !noNoisy do exitCode := 1
          else
            IO.println s!"ℹ️  {t} {elapsed}"
            unless !noNoisy do exitCode := 1
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
    IO.println "\nFailed tests:"
    for (code, t, out) in jobs do
      if code != 0 then
        IO.println s!"❌ {t}"
        unless out.stdout.isEmpty do IO.eprintln out.stdout
        unless out.stderr.isEmpty do IO.eprintln out.stderr
  let resultMarker := if succeeded == total then "✅" else "❌"
  IO.println s!"\nSuccessful tests: {succeeded} / {total} {resultMarker}"
  exit exitCode
