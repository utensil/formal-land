---
name: ut-lean-review-checklist
description: Checkable Lean-specific review checklist for ut-lean-review. Binding and scope, import ownership, names and docstrings, proof quality, post-revision recheck, and pipeline behavior.
---

# ut-lean-review checklist

## Binding and scope

- [ ] Recorded exact base, head, declared prerequisites, and changed paths.
- [ ] Inspected the complete aggregate diff, not only the latest commit.
- [ ] Verified the pull-request body states the actual scope, exclusions, grounding, dependencies, and nontrivial verification.
- [ ] Classified every finding as blocking, nonblocking, or optional; no unperformed check converted into a pass.

## Import ownership

- [ ] Every public declaration's defining types and structures come from direct public imports.
- [ ] No declaration compiles only through a transitive import.
- [ ] No generic module imports a later specialization.
- [ ] Moving a theorem would not change what downstream files receive.
- [ ] Removal probes or import-only compile probes used where the build alone is ambiguous.

## Names and docstrings

- [ ] Public names oriented to current mathlib conventions, including predicate-first forms.
- [ ] Names tested against the next planned models and equivalences, not only current files.
- [ ] No docstring calls an arbitrary element central.
- [ ] No docstring calls an endomorphism a projection before idempotence is proved.
- [ ] No docstring calls a construction canonical when it depends on selected data.
- [ ] Every public declaration has a concise, mathematically accurate docstring and a clear user-facing role; otherwise it is private.

## Proof quality

- [ ] No sorry, admit, warnings, or unintended files.
- [ ] No re-derivation of mathlib API; the proof was searched by structure first.
- [ ] Theorems stated at natural generality; no fixed-degree over-specialization where the argument is uniform.
- [ ] Simp equations shipped with the definition; orientation settled by the linter output, not by preference.
- [ ] Undocumented change, show, or rfl steps over quotient, graded, or typeclass wrappers either named as lemmas or commented.

## Post-revision recheck

- [ ] Old and new public declarations compared.
- [ ] Consumers of moved or renamed names searched.
- [ ] Direct imports verified with targeted builds.
- [ ] Complete build run.
- [ ] Exact aggregate diff and resulting commits inspected.
- [ ] Remote branch and pull-request state read back.

## Pipeline behavior

- [ ] Implement, contest, or wait ledger kept per finding at an exact head.
- [ ] Wrong prescriptions contested with a pinned probe (deletion probe, full linter output), not a repair loop.
- [ ] Interacting requests combined into one candidate; no alternating fix and revert commits.
- [ ] Contradictory findings answered with one concise evidence-backed contest quoting the conflicting rubric.
- [ ] Response scaled to change: full gate for API-surface changes; focused build and diff-scoped review for small repairs.
