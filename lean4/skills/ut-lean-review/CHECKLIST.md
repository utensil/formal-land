---
name: ut-lean-review-checklist
description: Checkable extension checklist for ut-lean-review, run after the latest Tau Ceti rubrics. Review process extensions (COORDINATION.md, _common.md) and quality extensions, one per rubric, plus structural checks the rubrics do not carry.
---

# ut-lean-review checklist

Run in order: the project's own review-process rules when it specifies them,
then the latest Tau Ceti rubrics (the default gate), then Tau Ceti
coordination for the process, then this extension checklist. Do not re-report
what CI and the linters enforce (build, axiom audit, linter set, import
boundary).

## Cannot miss

- [ ] Verdict bound to one exact head; a new commit received a fresh review.
- [ ] Aggregate diff inspected, not only the latest commit.
- [ ] No fixed-case statement of a uniform argument accepted as final scope.
- [ ] No duplicate in disguise (same content up to definitional spelling, symmetry, or duality) left standing.
- [ ] No docstring overclaiming left standing.
- [ ] Proofs probed for robustness; none rests on an implementation accident.

## Review process extensions

Extends COORDINATION.md Section 2 (head-bound verdicts):

- [ ] Exact base, head, declared prerequisites, and changed paths recorded.
- [ ] Complete aggregate diff inspected; findings classified blocking, nonblocking, or optional.
- [ ] No unperformed check converted into a pass.

Extends COORDINATION.md Section 2 (post-revision recheck) — after every revision:

- [ ] Old and new public declarations compared.
- [ ] Consumers of moved or renamed names searched.
- [ ] Direct imports verified with targeted builds.
- [ ] Complete build run; exact aggregate diff and remote branch state read back.

Extends `_common.md` (contested findings):

- [ ] Implement, contest, or wait ledger kept per finding at an exact head.
- [ ] Wrong prescriptions contested with a pinned probe (deletion probe, full linter output), not a repair loop.
- [ ] Contest replies to the exact review comment that raised the finding, names the exact head and compiler evidence, and reproduces the full lint result locally first.
- [ ] No lint exception added where a named non-simp theorem is retained (for example a `@[simp]` the `simpNF` normal form already reduces).
- [ ] Interacting requests combined into one candidate; no alternating fix and revert commits.
- [ ] A repeated logical finding triggered a whole-thread and consumer-contract review before a second public revision.
- [ ] Response scaled to the change: full gate for API-surface changes; focused build and diff-scoped review for small repairs; byte-identical verification, not fresh mathematical review, for source-equivalent rebases and message-only rewrites.

## Quality extensions, one per rubric

Extends reuse.md:

- [ ] New declarations searched by structure before writing (ut-lean-recon owns the procedure), not first at review time.
- [ ] No lemma re-proved from scratch that Mathlib or the library already carries.

Extends generality.md:

- [ ] Uniform arguments stated uniformly; fixed-degree or fixed-case specializations probed by generalizing and recompiling.

Extends proof-quality.md:

- [ ] Proofs perturbed and rebuilt (hypothesis change, lemma rename, definition move); brittle proofs given an explicit lemma or comment.

Extends documentation.md:

- [ ] No docstring calls an arbitrary element central, an endomorphism a projection before idempotence, or a construction canonical when it depends on selected data.

Extends naming.md:

- [ ] Public names tested against the next planned models and equivalences, not only the current files.

Extends placement.md:

- [ ] Suspect imports decided by removal probes or import-only compile probes, not guessing; no generic module imports a later specialization.

## Checks the rubrics do not carry

- [ ] Stack separated from the change: GitHub-visible diff and the change's own diff against its integration base both recorded.
- [ ] Module boundaries justified by a real planned consumer needing one without the other; the four pre-split questions answered.
- [ ] Import-free root not turned into a rolling re-export; aggregators have an explicit ownership contract.
