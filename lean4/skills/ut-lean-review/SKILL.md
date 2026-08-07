---
name: ut-lean-review
description: Review checklist for Lean pull requests in rubric-driven repositories (such as TauCeti), applied after the project rubrics: exact-head binding, import ownership, naming orientation, docstring-hypothesis traps, the post-revision recheck, and the contest protocol for an iterative review pipeline.
---

# ut-lean-review

## Purpose

Pull requests in rubric-driven repositories are judged against universal and per-change rubrics (TauCeti's live at TauCetiProject/TauCetiReview, see the pointer section below). This skill does not restate those rubrics. It adds the additional review checks the universal rubrics do not carry: process discipline (exact-head binding, the post-revision recheck, the contest protocol, proportional response) and Lean-culture checks (import ownership, naming orientation). It also records the behavior expected inside an iterative review pipeline where findings arrive one round at a time.

The order is fixed: first subject the change to the project rubrics, then run the additional checks below. The rubrics are the floor, the checks in this skill the ceiling on top of them, so a review that follows this skill already passes the TauCeti rubrics and then covers the ground those rubrics do not reach.

## When to use

Use this skill when reviewing a Lean pull request against the project rubrics, when responding to a review finding, or when preparing a change that will go through the review pipeline. It applies to Lean code in TauCeti and similarly run mathlib-based repositories, and it references rather than replaces the project rubrics.

## Additional checks

Run these after the project rubrics: the rubric verdict comes first, then this pass for what the rubrics do not carry.

### Exact-head binding

A verdict is bound to the exact reviewed commit. Record the exact base, head, declared prerequisites, and changed paths. Inspect the complete aggregate diff, not only the latest commit, since the latest commit alone can hide a change introduced several commits back. Classify every finding as blocking, nonblocking, or optional, and never convert an unperformed check into a pass.

### Import ownership

A declaration must compile through direct public imports, not through a transitive import it happens to inherit. A generic module must not import a later specialization, and a lower layer must not appear to depend on an optional presentation merely because one later module does. Removal probes and small import-only compile probes are more reliable than guessing from the current build.

### Name orientation

Check public names against current mathlib conventions, including predicate-first forms such as isIdempotentElem_* and conclusion-oriented names. A locally clear name can become ambiguous against the next planned construction, so name against the next model, not only the current file.

### Docstring-hypothesis traps

Check every docstring against the statement it accompanies. Do not call an arbitrary element central, an endomorphism a projection before idempotence is proved, or a construction canonical when it depends on selected data. Overclaimed docstrings are a common way a review misses a real dependency.

### Post-revision recheck

After a revision in response to review, recheck the old and new public declarations, the consumers of moved or renamed names, direct imports with targeted builds, the complete build, the exact aggregate diff, and the remote branch state. A later commit requires another review of the changed head.

## Responding to an iterative review pipeline

Keep an implement, contest, or wait ledger with one entry per finding, bound to an exact head. The compiler and the linter are the arbiter: contest a wrong prescription with a pinned probe, for example a deletion probe or the full linter output, rather than a repair loop that mutates the code hoping the finding stops firing. Combine interacting requests into one candidate instead of alternating fix and revert commits. When two findings contradict, the sole public reply is one concise evidence-backed contest that quotes the conflicting rubric wording and shows why both cannot hold.

Respond proportionally. An API-surface change runs the full gate: full build, audits, and full rubric review. A small, delimited repair that changes few lines and no API surface runs a focused build, the affected consumer probes, and a diff-scoped review. Do not re-run the entire gate ceremony for a handful of changed lines.

## Pointer section

The universal and per-change rubrics live at TauCetiProject/TauCetiReview/rubrics/. Mathlib naming, style, and contribution documentation lives at leanprover-community.github.io/contribute. Link to these; do not copy their content into this skill. For the golf-side discipline this review side checks, see the ut-lean-golf skill.## References

- CHECKLIST.md in this skill directory: the additional review checklist in checkable form.
- TauCetiProject/TauCetiReview/rubrics/: the universal and per-change rubrics.
- leanprover-community.github.io/contribute: mathlib naming and style.
- ut-lean-golf: the proof-golf discipline reviewed here.
