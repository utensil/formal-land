---
name: ut-lean-bump
description: "Bump a Lean project to a new pinned toolchain pair (Lean + mathlib + dependencies): establish the version ceiling, update the pins, resolve transitive pin conflicts, recover the cache, fix API drift against the changelog, and port tooling that elaborates against the active toolchain."
---

# ut-lean-bump: bumping the pinned toolchain pair

## Purpose

Bumping a Lean project means moving the pinned pair (Lean version, mathlib revision, dependency revisions) to a newer target and making the project compile and pass on it. This skill covers the mechanics that turn a bump from guesswork into a reproducible operation: choosing the target, resolving pin conflicts, recovering caches, tracing renamed API through the changelog, and handling tooling that lags the new pair. It complements ut-lean-ops, which owns running and verifying the project once it is pinned.

## When to use

- Moving a project from one Lean/mathlib pair to another.
- Adopting a new stable release or a dependency-forced lower bound.
- Porting project code and tooling after the core API changed between versions.
- Any time a build that "worked before" fails with renamed or moved identifiers.

## Procedure

### 1. Establish the version ceiling

The target is bounded by the newest release of every dependency:

- A stable pair means Lean and mathlib releases in lockstep: mathlib tags `v4.x.y` for each stable Lean release, and the tag's own `lean-toolchain` names the exact Lean version it was tested with. Read the tag, not the branch: `git ls-remote` the tags of each repo and fetch each candidate tag's `lean-toolchain`.
- The newest stable Lean release that has a matching mathlib tag is the ceiling. `master`/`main` branches are not candidates: they track release candidates.
- Every dependency sets a lower bound: a dependency whose newest release (or whose `master` toolchain) only supports an older Lean caps the whole project. Take the latest stable; when a dependency cannot go higher, settle on the dependency's bound. A dependency tracking a release candidate makes that rc an acceptable lower bound; otherwise prefer the latest stable.
- Record the chosen pair as explicit tags/commits, not floating branches: `require <dep> from git "<url>" @ "<tag>"` or a pinned commit. The manifest then records the exact revisions — treat the manifest as the pin.

### 2. Update the pins

- Write the new Lean version to `lean-toolchain` (e.g. `leanprover/lean4:v4.32.2`).
- Update every `require` line in `lakefile.lean`/`lakefile.toml` to the new tag or commit, one dependency at a time.
- Run `lake update` to regenerate `lake-manifest.json`, and read the resolved revisions back: they must match the intended tags.

### 3. Resolve transitive pin conflicts

- A tagged parent release ships with the transitive revisions it was tested against — which need not equal that dependency's matching tag. For example, a mathlib release may pin batteries at the previous minor's tag commit even though a batteries tag with the same number exists.
- When two parents pin different revisions of the same transitive package, `lake update` prints a mismatch warning and, worse, `lake exe cache get` computes wrong hashes for the package whose pin lost.
- Lake resolves conflicting transitive pins by declaration order in the root lakefile: the parent whose pins should win must be declared last (the mismatch message says so explicitly). Reorder the `require`s and re-run `lake update`; verify the resolved revision in the manifest matches the winning parent's manifest.

### 4. Recover the cache

- mathlib's automatic post-update cache fetch (a `post_update` hook) can report success while placing nothing: it runs before the package checkouts are fully in place, leaving an empty build tree. A green `lake update` does not mean the cache landed.
- After `lake update`, re-run `lake exe cache get` manually and confirm the dependency's `.olean` directory actually has content (e.g. `find .lake/packages/<lib>/.lake/build -name '*.olean' | wc -l`).
- If a module reports "object file ... does not exist" for an import, it may not be covered by the cache at all: the cache covers only the imports the dependency library itself uses. Deprecated umbrella modules and rarely-used roots of dependency packages are typically absent. Prefer importing the cached subsets the dependency itself imports, or build the missing module explicitly and check whether it was quick (from source) — that tells you whether a fresh checkout would fail.

### 5. Build and test

- A green `lake build` proves only the default target's import closure. Projects whose acceptance is per-file elaboration (test drivers that compile every file) exercise far more surface: run the full test driver, not just the build.
- Evaluate with `LEAN_ABORT_ON_PANIC=1` set: CI-style environments set it, and v4.32-era runtime checks (e.g. panicking on `mainOnly` environment-extension modification from a declaration's async context) abort the process under it even when a plain local run only logs the panic as an info message.
- Prefer `#eval!` over `#eval` for IO primitives backed by opaque (sorry-based) core implementations; plain `#eval` aborts on them.

### 6. Fix API drift with the changelog

Between versions the API churns, and error messages, names, and module paths all drift. Treat every displaced `#check` as substantial: it confirms a theorem, instance, class, or type exists in mathlib, and the goal is to find what it became, not a nearest neighbor.

- Grep the pinned checkout first: `grep -rn` the new source for the concept or a remembered fragment of the name.
- Use the mathlib checkout's history (Lake clones are full): `git log --oneline -S 'oldName' -- <path>` finds the rename/removal commit; `git show <commit> -- <path>` shows the diff and the new name. mathlib's own `Changes`-style commits and deprecation-removal commits are common culprits.
- The catalog below lists the drift patterns observed across Lean 4.16–4.32; check it before re-deriving a fix.
- Only when the theorem was genuinely removed upstream (no successor in the new source) is commenting the `#check` with the closest survivor acceptable — and say so in a comment.
- Behavior changes are not always breakage: a test that used to error may now compile because the underlying bug was fixed. Re-baseline guarded expected messages against the new pair and document the fix; do not delete the example.

### 7. Port tooling that elaborates against the active toolchain

Doc and annotation generators build against the active toolchain and lag the new pair; they are part of the bump surface.

- Check for an updated fork before porting: `gh api repos/<owner>/<repo>/forks?sort=newest`, and read each candidate fork's `lean-toolchain`. The newest fork may still be several releases behind the new core API reworks.
- Port against the changed core APIs (see catalog); keep the port on a fork branch and clone it in the project's tooling install script, so CI builds it per project.
- Some tooling derives the search path by asking the build tool (e.g. `lake setup-file`); its output schema changes across versions and may stop reporting the path entirely. Deriving the `.olean` search path from the standard build directories (project `.lake/build/lib/lean` plus each `.lake/packages/*/.lake/build/lib/lean`) is a robust substitute; keep the build-tool call for its dependency-building side effect.
- Treat the tool's output as a deliverable: a broken annotation/docs pipeline should surface as a failing run, not be silently skipped.

### 8. Verify and record

- Re-run every test driver; run audits (no new `sorry`/`admit`, axioms on the allowlist); regenerate and commit the manifests.
- After regeneration, search tracked files for each previous pinned revision
  and explain every surviving hit as intentional history or stale metadata.
- Record the toolchain readback, the resolved revisions, the commands, and the exit codes so the bump is reproducible from a fresh checkout.

## API drift catalog (Lean 4.16 → 4.32)

Patterns observed across Lean core and mathlib during a multi-release bump; re-check against the pinned source before applying.

- Namespace moves: `Basis` → `Module.Basis`; `Name` → `Lean.Name` (with `open Lean` making the short name work again); `FuzzyMatching` moved from tactic code into `Lean.Data.FuzzyMatching`; `realPathNormalized` folded into `Lean.Util.Path`; `Lean.Util.Paths` removed entirely.
- Instance renames: anonymous instances get auto-names (e.g. `CliffordAlgebra.instRing` → `instRingCliffordAlgebra`); named instances re-`inst*`-ed (`Module.End.semiring` → `Module.End.instSemiring`). `#synth` prints the resolved instance name — read it back for the `#check`.
- Module moves and splits: `Mathlib.Data.Matrix.Notation` → `Mathlib.LinearAlgebra.Matrix.Notation`; `Mathlib.LinearAlgebra.Matrix.Spectrum` → `Mathlib.Analysis.Matrix.Spectrum`; `Mathlib.Data.Complex.FiniteDimensional` → `Mathlib.LinearAlgebra.Complex.FiniteDimensional`; `Mathlib.Algebra.BigOperators.Ring` split into `BigOperators.Ring.Finset` etc.; `Mathlib.LinearAlgebra.Basis` split into `Basis.Defs`/`Basis.Basic`/...; `Mathlib.Data.List.Sort` owns the sortedness predicates.
- Removed core names and successors: `List.Sorted` → `SortedLT`/`SortedLE` (needs `Preorder`); `DirectSum.GradeZero.module` → scoped instances under `open DirectSum` (for submodule gradings: `SetLike.GradeZero.instSemiring` and friends); `CompleteLattice.Independent` → `iSupIndep` (so `eigenspaces_independent` → `eigenspaces_iSupIndep`); `List.maximum?` → `List.max?`; `List.enum` → `List.zipIdx` (pair order swaps!); `List.join` → `List.flatten`; `String.drop` returns `String.Slice`; `RingQuot.mk` survives (structure constructor) but may drop out of import scope.
- `String.Pos` rework: positions are now `String.Pos.Raw` (plain `{ byteIdx : Nat }`); `String.Pos s` is the validated, string-indexed form used by `String.extract`. There is no position-minus-position; do byte-index arithmetic. `String.Pos.Raw.extract` exists for raw-position slicing.
- Message-format churn: `unknown identifier 'x'` → ``Unknown identifier `x` ``; `type mismatch` → `Type mismatch`; the `: Type` suffix on elaborated types is dropped. Re-baseline guard docs against the new pair.
- `#guard_msgs` spec syntax: `(dropInfo := true)` is gone; use filter specs like `(drop info, check error)`.
- `IO` is no longer an `EStateM`: `EStateM.get` no longer typechecks in `IO` blocks; `EStateM.get : EStateM ε σ σ` survives for other monads.
- Runtime checks: modifying a `mainOnly` environment extension from a declaration's async context panics (and aborts under `LEAN_ABORT_ON_PANIC=1`); registering such extensions with `asyncMode := .local` permits the modification.
- Tooling: `lake setup-file` output changed schema (no longer reports the search path; takes the target file); `Lean.Util.LakePath.determineLakePath` locates `lake`.

## References

- ut-lean-ops (pinned-toolchain run and verification; the acceptance gate the bump must pass)
- ut-lean-recon (pinned-revision reconnaissance against the new pin)
- mathlib release tags and toolchains: <https://github.com/leanprover-community/mathlib4>
- Lean release tags: <https://github.com/leanprover/lean4>
- Lake documentation: <https://github.com/leanprover/lean4/blob/master/src/lake/README.md>
