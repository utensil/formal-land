---
name: ut-lean-review-checklist
description: Checkable additional review checklist for ut-lean-review, run after the project rubrics. Review protocol per the repository coordination contract, and Lean and math quality checks: structural, imports, names, docstrings, reuse by structure, generality and robustness probes, post-revision recheck, and pipeline behavior.
---

# ut-lean-review checklist

Run in order: first the latest Tau Ceti rubrics (the default quality gate for
all math formalization reviews), then this additional pass. The rubric
verdict is the floor; this list covers what the rubrics do not carry. The
review protocol follows Tau Ceti coordination (COORDINATION.md Section 2 and
the rubrics' `_common.md`) unless the project specifies its own
review-process rules, which then take precedence.

## Review protocol

- [ ] Verdict bound to the exact head; a new commit requires a fresh review.
- [ ] Recorded exact base, head, declared prerequisites, and changed paths.
- [ ] Inspected the complete aggregate diff, not only the latest commit.
- [ ] Verified the pull-request body states the actual scope, exclusions, grounding, dependencies, and nontrivial verification.
- [ ] Classified every finding as blocking, nonblocking, or optional; no unperformed check converted into a pass.

## Structural checks

- [ ] Stack separated from the change: GitHub-visible diff and the change's own diff against its integration base both recorded.
- [ ] Module boundaries justified by a real planned consumer needing one without the other; no split merely because GitHub includes prerequisites.
- [ ] The four pre-split questions answered (real dependency, stable responsibility, no cycle, sensible without this PR).
- [ ] Import-free root not turned into a rolling re-export; aggregators have an explicit ownership contract.

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

## Reuse by structure

- [ ] New declarations searched by mathematical structure, not only by name; a third definitional-equality spelling of an existing theorem counts as duplication.
- [ ] No lemma re-proved from scratch that Mathlib already carries.

## Proof quality

- [ ] No sorry, admit, warnings, or unintended files.
- [ ] Theorems stated at natural generality; no fixed-degree over-specialization where the argument is uniform (generalize and recompile to probe).
- [ ] Proofs probed for robustness: a hypothesis change, lemma rename, or definition move must not break them; brittle proofs get an explicit lemma or comment.
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

- [ ] Ledger kept per finding at an exact head (implement, contest, or wait).
- [ ] Wrong prescriptions contested with a pinned probe (deletion probe, full linter output), not a repair loop.
- [ ] Interacting requests combined into one candidate; no alternating fix and revert commits.
- [ ] Contradictory findings answered with one concise evidence-backed contest quoting the conflicting rubric.
- [ ] Response scaled to change: full gate for API-surface changes; focused build and diff-scoped review for small repairs.
