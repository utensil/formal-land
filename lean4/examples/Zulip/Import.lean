/-

From https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Lean4.20autocomplete

Will have to keep on fiddling the topic of meta-programming, syntax and dealing with files in Lean

related:

- https://github.com/utensil/LeanBlueprintExample/blob/main/Exe/Decls.lean
- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/get.20filename.20.2B.20pos

-/

import Std.Tactic.TryThis

namespace Mathlib.Tactic.imp

open Lean Elab Command FuzzyMatching System

/-- Infer module name of source file name. -/
def moduleNameOfFileName (fname : FilePath) (rootDir : Option FilePath) : IO Name := do
  Lean.initSearchPath (<- Lean.findSysroot) [(<-IO.currentDir) / "lake-packages/mathlib/"]
  let fname ← IO.FS.realPath fname
  let rootDir ← match rootDir with
    | some rootDir => pure rootDir
    | none         => IO.currentDir
  let mut rootDir ← realPathNormalized rootDir
  if !rootDir.toString.endsWith System.FilePath.pathSeparator.toString then
    rootDir := ⟨rootDir.toString ++ System.FilePath.pathSeparator.toString⟩
  if !rootDir.toString.isPrefixOf fname.normalize.toString then
    throw $ IO.userError s!"input file '{fname}' must be contained in root directory ({rootDir})"
  -- NOTE: use `fname` instead of `fname.normalize` to preserve casing on all platforms
  let fnameSuffixComponents := fname.withExtension "" |>.components.drop (rootDir.components.length + 1)
  let modName    := fnameSuffixComponents.foldl Name.mkStr Name.anonymous
  pure modName

/--  A syntax that allows strings to be printed without surrounding them by guillemets `«...»`. -/
declare_syntax_cat write_me_output_stx

@[inherit_doc Parser.Category.write_me_output_stx]
syntax "import " ident : write_me_output_stx

/-- `imp <string>` tries to find a file matching `Mathlib.<string>`.
It prints a list of candidates, taking the names from `Mathlib.lean`.
If there is only one candidate, it suggests `import Mathlib.<uniqueCandidate>` as a `Try this`.

Using `imp! <string>` uses fuzzy-matching, rather than exact matching. -/
elab (name := commandImp!) tk:"imp" fz:("!")? na:(colGt ident) : command => do
  let inp := na.getId.toString
  let dat := (← IO.FS.lines "lake-packages/mathlib/Mathlib.lean").map (String.drop · 15)
  let cands := dat.filter <| (if fz.isSome then fuzzyMatch else String.isPrefixOf) inp

  liftTermElabM do
    cands.toList.forM fun imp => do
      let impS ← moduleNameOfFileName ("lake-packages/mathlib/Mathlib/" ++ imp.replace "." "/" ++ ".lean") "lake-packages/mathlib/"
      let imp : TSyntax `write_me_output_stx ← `(write_me_output_stx| import $(mkIdent impS))
      let stx ← getRef
      Std.Tactic.TryThis.addSuggestion stx imp


@[inherit_doc commandImp!]
macro "imp!" na:(colGt ident) : command => `(command| imp ! $na)

end Mathlib.Tactic.imp

imp! Ring