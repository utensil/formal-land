---
name: ut-lean-ops
description: "Run and verify a Lean project at the toolchain level: pinned Lean and mathlib, cache-first builds, no-sorry and axiom audits, fresh-checkout reproduction, and the verification discipline for executable Lean content."
---

# ut-lean-ops: running and verifying a Lean project

## Purpose

Lean projects have a reproducible toolchain story (toolchain file, Lake manifest, mathlib cache) and an evidence story (audits, reproduction, a verification chain). This skill covers the low-level mechanics: set up a project, pin its dependencies, build from cache, audit the source, and reproduce results from a fresh checkout. It also records how to be truthful about what verification claims follow from what evidence, especially for executable and numerical content.

## When to use

- Setting up or checking a Lean project that depends on mathlib.
- Deciding whether a build result is trustworthy enough to report.
- Writing the acceptance check for a Lean change: what must pass and what must be recorded.
- Adding executable content (`native_decide`, arrays, foreign function interfaces) and needing to state exactly what is proved.
- Any time "it builds" would otherwise be the whole story.

Out of scope: coordinating parallel work, managing branches or worktrees, monitoring, scheduling, and chat relay. Those are separate concerns.

## Procedure

### 1. Set up the project

- `lean-toolchain` pins the Lean version, for example `leanprover/lean4:v4.16.0`.
- `lakefile.toml` declares the packages and the mathlib requirement with its branch, usually `master`.
- The exact mathlib commit is recorded in `lake-manifest.json`, not in the lakefile. Treat the manifest as the pin: two checkouts with the same manifest and toolchain resolve the same dependency.
- Pin deliberately. A stable toolchain pair (Lean version plus the mathlib commit it is tested against) is the starting point of any reproducible run. When a new pair is adopted, re-verify the project on it; old results do not carry over by assumption.
- Give the project a name in the lakefile (`name := ...`). Targets are then built with `lake build <Name>`.

### 2. Build from cache

Mathlib is large. The normal flow is:

```bash
lake exe cache get     # fetch the prebuilt mathlib cache for the pinned manifest
lake build             # compile only your project against cached .olean files
lake build --iofail    # fail on any error reported by a command in an IO macro
```

- Run `lake exe cache get` before every build. Its exit code, not the later `lake build` result, determines whether the cache was available.
- Your project compiles from source; mathlib does not. If a mathlib source target appears in the build log, the cache did not cover the pin and the run must stop and be redone.
- Clean your own build artifacts before rebuilding (`lake clean`), and confirm your own `.olean` and `.ilean` files are gone before `lake build`. A stale artifact from a previous source state must not be able to make a change look green.

### 3. Audit the source

A proof accepted by the kernel still deserves a source-level audit:

- Scan the project source for `sorry` and `admit`; the scan must return no matches.
- Scan for `axiom` declarations. Any axiom must be on an approved allowlist of exact declaration names. Substring matches are forbidden, and the default allowlist is empty.
- Mathlib declarations are imported, not project axioms. To hold the project to the kernel-minimal bar, check the allowlist against the permitted set `propext`, `Classical.choice`, `Quot.sound`.
- `#print axioms <theorem>` reports the axiom closure of a single theorem and works everywhere, even where sandboxed tooling does not.
- Record the commands and their exit codes with the results. An audit that cannot be reproduced is not an audit.

### 4. Reproduce from a fresh checkout

The reproduction rule: a cache hit can never turn a failing item green. The cache only removes mathlib compile time; your project still compiles from source every time. A claim holds only when, from a fresh checkout:

- dependencies are restored with `lake exe cache get`,
- only the intended targets are built,
- the source audit passes,
- every executable oracle or concrete example is run, and
- the exact Lean and mathlib revisions are recorded.

Record the toolchain and manifest readback, the commands, the exit codes, the build logs, and hashes of produced artifacts. Report any environmental deviation. Cache unavailability, an incomplete cache, or a mathlib source compilation fails the reproduction gate.

### 5. State what the verification chain proves

For a project with executable content, keep the layers distinct and prove the bridges between them. The full chain is in VERIFY.md in this directory.

## References

- Lean manual quickstart: https://lean-lang.org/lean4/doc/quickstart.html
- Lake documentation: https://github.com/leanprover/lean4/blob/master/src/lake/README.md
- mathlib: https://github.com/leanprover-community/mathlib4
- VERIFY.md in this directory: the verification discipline for executable Lean content.
