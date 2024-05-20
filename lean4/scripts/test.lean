/-
This is adapted from https://github.com/leanprover-community/batteries/blob/078ac74e3157bd7b02628eca0260faa234878b2a/scripts/test.lean
with my own customizations on paths, options and summary output.
-/
open IO.Process
open System

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Force.20a.20Lean.20evaluation/near/338717704
def time (f : IO α) : IO (String × α) := do
  let pre ← IO.monoMsNow
  let ret ← f
  let post ← IO.monoMsNow
  let monoMs := post - pre
  let seconds := monoMs.toFloat / 1000.0
  let elapsed := s!"{seconds}s"
  pure (elapsed.replace "000s" "s", ret)

/--
Run tests.

If no arguments are provided, run everything in `examples/` and `exmaples/Zulip`.

If arguments are provided, they are interpreted as test names in `examples/`, e.g.

- `lake exe test Hello` runs `examples/Hello.lean`
- `lake exe test Zulip/Agatha` runs `examples/Zulip/Agatha.lean`

Allow tests to produce output by default, use the flag `no-noisy` to disallow any output on stdout or stderr.
-/
def main (args : List String) : IO Unit := do
  let cwd := mkFilePath ["."] -- ← IO.currentDir

  -- We first run `lake build`, to ensure oleans are available.
  -- Alternatively, we could use `lake lean` below instead of `lake env lean`,
  -- but currently with parallelism this results in build jobs interfering with each other.
  _ ← (← IO.Process.spawn { cmd := "lake", args := #["build"] }).wait

  -- Collect test targets by walking `examples/` and `exmaples/Zulip`.
  let noNoisy := args.contains "--no-noisy"
  let enter : FilePath → IO Bool := fun path ↦ pure <| path.fileName != "NoCI"
  let targets := (<- match args.erase "--no-noisy" with
  | [] => do return (← System.FilePath.walkDir (enter := enter) <| cwd / "examples") ++
                  (← System.FilePath.walkDir (enter := enter) <| cwd / "examples" / "Zulip")
  | _ => pure <| (args.map fun t => mkFilePath [cwd.toString, "examples", t] |>.withExtension "lean") |>.toArray)
  let existing ← targets.filterM fun t => do pure <| (← t.pathExists) && !(← t.isDir) && (t.extension.getD "" == "lean")
  let tasks : Array (Task (Except IO.Error (FilePath × Output))) ←
    existing.mapM fun t => do
      IO.asTask do
        let ⟨elapsed, out⟩ ← time <| IO.Process.output
          { cmd := "lake",
            args := #["env", "lean", t.toString],
            env := #[("LEAN_ABORT_ON_PANIC", "1")] }
        let mut exitCode := out.exitCode
        if exitCode == 0 then
          if out.stdout.isEmpty && out.stderr.isEmpty then
            IO.println s!"✅ {t} {elapsed}"
          else
            IO.println s!"ℹ️ {t} {elapsed}"
            unless !noNoisy do exitCode := 1
        else
          IO.eprintln s!"❌ {t} {elapsed}"
        -- unless out.stdout.isEmpty do IO.eprintln out.stdout
        -- unless out.stderr.isEmpty do IO.eprintln out.stderr
        pure ⟨t, out⟩
  -- Wait on all the jobs and exit with 1 if any failed.
  let mut exitCode : UInt8 := 0
  let mut total := 0
  let mut succeeded := 0
  let mut failed : Array (FilePath × IO.Process.Output) := #[]
  for t in tasks do
    let e ← IO.wait t
    total := total + 1
    match e with
    | .error f => IO.eprintln s!"❌ {f}"
    | .ok ⟨path, out⟩ =>
      if out.exitCode == 0 then
        succeeded := succeeded + 1; pure ()
      else
        failed := failed.push (path, out); exitCode := 1

  if failed.size != 0 then
    IO.println "\nFailed examples:"
    for (t, out) in failed do
      IO.println s!"❌ {t}"
      unless out.stdout.isEmpty do IO.eprintln out.stdout
      unless out.stderr.isEmpty do IO.eprintln out.stderr
  let resultMarker := if succeeded == total then "✅" else "❌"
  IO.println s!"\nSuccessful examples: {succeeded} / {total} {resultMarker}"
  exit exitCode
