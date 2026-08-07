---
name: ut-lean-ops
description: "Run and verify a Lean project at the toolchain level: slice worktrees, pinned Lean and mathlib, cache-first builds with cache reuse, no-sorry and axiom audits, fresh-checkout reproduction, and the verification discipline for executable Lean content."
---

# ut-lean-ops: running and verifying a Lean project

## Purpose

Lean formalization projects have a reproducible toolchain story (toolchain file, Lake manifest, mathlib cache) and an evidence story (audits, reproduction from a fresh checkout). This skill covers the low-level mechanics every mathlib-based project needs: set up a project, pin its dependencies, build from cache, audit the source, and reproduce results from a fresh checkout. A scoped extension (SOFTWARE_VERIFICATION.md) adds the extra discipline for the minority of projects that also carry executable content; pure theorem libraries do not need it.

## When to use

- Setting up or checking a Lean formalization project that depends on mathlib.
- Starting a slice that needs its own checkout: create the worktree and check the machine can afford it.
- Deciding whether a build result is trustworthy enough to report.
- Writing the acceptance check for a Lean change: what must pass and what must be recorded.
- Any time "it builds" would otherwise be the whole story.
- Only if the project actually carries executable content (`native_decide`, arrays, foreign function interfaces): also read SOFTWARE_VERIFICATION.md for the executable verification chain.

Out of scope: coordinating parallel work across agents (claims, leases, task queues), monitoring, scheduling, chat relay, and the verification of executable programs. The last one is an extension (SOFTWARE_VERIFICATION.md), not part of the core; most formalization work never reaches it.

## Procedure

### 1. Set up the project

- `lean-toolchain` pins the Lean version, for example `leanprover/lean4:v4.16.0`.
- `lakefile.toml` declares the packages and the mathlib requirement with its branch, usually `master`.
- The exact mathlib commit is recorded in `lake-manifest.json`, not in the lakefile. Treat the manifest as the pin: two checkouts with the same manifest and toolchain resolve the same dependency.
- Pin deliberately. A stable toolchain pair (Lean version plus the mathlib commit it is tested against) is the starting point of any reproducible run. When a new pair is adopted, re-verify the project on it; old results do not carry over by assumption.
- Give the project a name in the lakefile (`name := ...`). Targets are then built with `lake build <Name>`.

### 2. Work on a slice in a worktree

Principles to be aware of:

- Git worktrees give each slice its own checkout of the same repository, with its own dependency tree under `.lake/packages`.
- Every worktree hydrates that tree itself: on the order of seven gigabytes for a mathlib project, plus its build products, and the builds it runs use CPU and memory.
- The compressed mathlib cache archives are shared across worktrees (section 3); the unpacked dependency products are per-checkout.

Recommended practice:

- Work on each slice in its own git worktree at a conventional root, by default `~/worktrees/` unless the user specifies another location. The main checkout holds the canonical branches and is not a slice workspace.
- Before creating each new worktree, check the machine can afford it: free disk with `df -h`, and CPU and memory headroom for the builds the slice will run.
- To limit disk use, retain only the live worktrees from the same route (see ut-lean-roadmap for route) and remove finished ones with `git worktree remove`; never remove a worktree belonging to another route or another project, whose work must not be broken. `git worktree prune` clears stale bookkeeping.
- The reproduction rule (section 5) applies per worktree: a reused cache never turns a failing item green, and the fresh-checkout gate runs in a clean worktree.

### 3. Build from cache

Mathlib is large. The normal flow is:

```bash
lake exe cache get     # fetch the prebuilt mathlib cache for the pinned manifest
lake build             # compile only your project against cached .olean files
lake build --iofail    # fail on any error reported by a command in an IO macro
```

- Run `lake exe cache get` before every build. Its exit code, not the later `lake build` result, determines whether the cache was available.
- Your project compiles from source; mathlib does not. If a mathlib source target appears in the build log, the cache did not cover the pin and the run must stop and be redone.
- Clean your own build artifacts before rebuilding (`lake clean`), and confirm your own `.olean` and `.ilean` files are gone before `lake build`. A stale artifact from a previous source state must not be able to make a change look green.
- Cache reuse across worktrees and projects: the compressed mathlib cache archives that `lake exe cache get` downloads are shared through the cache directory (by default `~/.cache/mathlib`), so the same pinned manifest downloads them once. The unpacked dependency products under `.lake/packages` and `.lake/build` are per-checkout, several gigabytes each, and are not shared.
- Do not symlink or hardlink another worktree's `.lake/packages` into your own to fake sharing: it creates hidden lifecycle coupling and a cleanup failure, since the target can be removed and the link then silently serves a stale tree. Hydrate each worktree normally.

### 4. Audit the source

A proof accepted by the kernel still deserves a source-level audit:

- Scan the project source for `sorry` and `admit`; the scan must return no matches.
- Scan for `axiom` declarations. Any axiom must be on an approved allowlist of exact declaration names. Substring matches are forbidden, and the default allowlist is empty.
- Mathlib declarations are imported, not project axioms. To hold the project to the kernel-minimal bar, check the allowlist against the permitted set `propext`, `Classical.choice`, `Quot.sound`.
- `#print axioms <theorem>` reports the axiom closure of a single theorem and works everywhere, even where sandboxed tooling does not.
- Record the commands and their exit codes with the results. An audit that cannot be reproduced is not an audit.

### 5. Reproduce from a fresh checkout

The reproduction rule: a cache hit can never turn a failing item green. The cache only removes mathlib compile time; your project still compiles from source every time. A claim holds only when, from a fresh checkout:

- dependencies are restored with `lake exe cache get`,
- only the intended targets are built,
- the source audit passes,
- every executable oracle or concrete example is run, and
- the exact Lean and mathlib revisions are recorded.

Record the toolchain and manifest readback, the commands, the exit codes, the build logs, and hashes of produced artifacts. Report any environmental deviation. Cache unavailability, an incomplete cache, or a mathlib source compilation fails the reproduction gate.

### 6. Executable content only: state what the verification chain proves

This section and SOFTWARE_VERIFICATION.md apply only to projects that carry executable content (computed programs, native oracles, float kernels). Pure formalization projects, whose deliverables are declarations and proofs, skip it entirely. For projects that do have executable content, keep the layers distinct and prove the bridges between them. The full chain is in SOFTWARE_VERIFICATION.md in this directory.

### 6. Bump the pinned toolchain pair

Adopting a new stable pair is itself a checkable operation:

- The ceiling is set by the newest release of every dependency. A dependency that tracks an older Lean, including a release candidate, bounds the whole project: take the latest stable release and settle on the dependency's bound when it cannot go higher.
- A tagged parent ships with the transitive revisions it was tested against, which need not equal the dependency's matching tag. When two parents pin different revisions of the same transitive package, `lake update` warns and cache hashes break: declare the parent whose pins should win last and re-run `lake update`.
- After `lake update`, verify the cache actually landed. The automatic post-update cache fetch can report success while package checkouts are not yet in place, leaving an empty build tree: re-run `lake exe cache get` manually and confirm the dependency olean directory has content.
- A green `lake build` proves only the default target's import closure, and the cache covers only the imports the dependency library itself uses. Files elaborated individually (test drivers that compile every file) reach outside that closure: prefer cached subsets over deprecated umbrella modules, and treat per-file elaboration as the acceptance surface.
- Between versions expect message-format churn, not only errors: expected-message specs, instance names, namespaces, and quoted identifier output all drift; re-baseline against the new pair rather than porting verbatim. Set `LEAN_ABORT_ON_PANIC=1` when evaluating to surface runtime panics CI-style runners hit, and prefer `#eval!` for IO primitives backed by opaque implementations.
- Tooling that elaborates against the active toolchain (doc/annotation generators) is part of the bump surface and may lag the new pair; gate it to degrade with a warning rather than reddening the run.

## References

- Lean manual quickstart: https://lean-lang.org/lean4/doc/quickstart.html
- Lake documentation: https://github.com/leanprover/lean4/blob/master/src/lake/README.md
- mathlib: https://github.com/leanprover-community/mathlib4
- SOFTWARE_VERIFICATION.md in this directory: the verification discipline for executable Lean content, gated on the project carrying executable content.
- Related skills: ut-lean-check (independent-kernel verification), ut-lean-recon (pinned-revision reconnaissance).
