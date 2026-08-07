---
name: ut-lean-review
description: Review for Lean pull requests in rubric-driven repositories (such as TauCeti), applied after the project rubrics: a review protocol grounded on the repository's coordination contract, plus Lean and math quality detection techniques (structural, imports, naming, docstrings, reuse-by-structure, robustness probes).
---

# ut-lean-review

## Purpose

Pull requests in rubric-driven repositories are judged against universal and per-change rubrics (TauCeti's live at TauCetiProject/TauCetiReview, see the pointer section below). This skill does not restate those rubrics. It adds two things the rubrics do not carry: the review protocol (how a review is bound, rechecked, and contested inside an iterative pipeline), and Lean and math quality detection techniques (how to find the problems the rubrics judge).

The order is fixed: first subject the change to the project rubrics, then run the additional pass below. The rubrics are the floor, the checks in this skill the ceiling on top of them, so a review that follows this skill already passes the TauCeti rubrics and then covers the ground those rubrics do not reach.

## When to use

Use this skill when reviewing a Lean pull request against the project rubrics, when responding to a review finding, or when preparing a change that will go through the review pipeline. It applies to Lean code in TauCeti and similarly run mathlib-based repositories, and it references rather than replaces the project rubrics.

## Review protocol

The process contract is not invented here: it is the repository's coordination contract, followed rather than restated. In Tau Ceti that is COORDINATION.md (Section 2, reading review state) together with the contested-findings protocol in the rubrics' `_common.md`. Other rubric-driven repositories substitute their equivalent coordination document.

### Exact-head binding

A review applies only to the head commit it names; a new commit needs a fresh review (Tau Ceti COORDINATION.md Section 2). Record the exact base, head, declared prerequisites, and changed paths. Inspect the complete aggregate diff, not only the latest commit, since the latest commit alone can hide a change introduced several commits back. Classify every finding as blocking, nonblocking, or optional, and never convert an unperformed check into a pass.

### Post-revision recheck

After a revision in response to review, recheck the old and new public declarations, the consumers of moved or renamed names, direct imports with targeted builds, the complete build, the exact aggregate diff, and the remote branch state. The review reads the review-state marker for the current head rather than a stale one.

### Contest and pipeline behavior

Keep an implement, contest, or wait ledger with one entry per finding, bound to an exact head. The compiler and the linter are the arbiter: contest a wrong prescription with a pinned probe, for example a deletion probe or the full linter output, rather than a repair loop that mutates the code hoping the finding stops firing. Combine interacting requests into one candidate instead of alternating fix and revert commits. When two findings contradict, the sole public reply is one concise evidence-backed contest that quotes the conflicting rubric wording and shows why both cannot hold, per the contested-findings protocol.

Respond proportionally. An API-surface change runs the full gate: full build, audits, and full rubric review. A small, delimited repair that changes few lines and no API surface runs a focused build, the affected consumer probes, and a diff-scoped review. Do not re-run the entire gate ceremony for a handful of changed lines.

## Lean and math quality checks

The rubrics judge the quality angles; these are the techniques for finding the problems they judge, plus structural checks the rubrics do not carry. Run them after the rubric verdict.

### Separate the stack from the change

A stacked pull request may display every unmerged prerequisite. Record both the GitHub-visible diff against the integration branch and the change's own diff against its exact integration base. The first determines the human dependency order; the second determines whether the change is structurally too large. Do not split a coherent change merely because GitHub includes prerequisite files.

### Organize around downstream consumers

Two groups of declarations deserve separate modules when later work needs one without the other. Before proposing a split, ask: does the boundary remove a real dependency for a planned consumer? does each resulting module have a stable mathematical responsibility? can the higher layer directly import the lower one without a cycle? would the split remain sensible if this pull request did not exist? If not, the split is file-count optimization rather than structure.

### Roots and aggregators as policy

An import-free root avoids a transitive catch-all API and conflicts among independent work streams. A feature pull request must not turn the root into a rolling re-export file, and aggregators, when introduced, need an explicit ownership and import contract rather than arising accidentally from whichever feature most recently touched the root.

### Imports as mathematical ownership

A public declaration's defining types and structures must be available through direct public imports. Proof-only tactics and calculations belong in private imports. Check whether a declaration compiles only because of a transitive import, whether a generic module imports a later specialization, whether moving a theorem changes what downstream files receive, and whether an import makes a lower layer appear to depend on an optional presentation. Removal probes and small import-only compile probes are more reliable than guessing from the current build.

### Name against the next model

Check public names against current mathlib conventions and against known future constructions. A locally clear name can become ambiguous against the next planned equivalence, action, or specialization, so name for the next model, not only the current file.

### Docstring-hypothesis traps

Check every docstring against the statement it accompanies. Do not call an arbitrary element central, an endomorphism a projection before idempotence is proved, or a construction canonical when it depends on selected data. Overclaimed docstrings are a common way a review misses a real dependency.

### Reuse by structure, not by name

A declaration that restates an existing theorem under a third definitional-equality spelling is duplication in disguise, even when no name matches. Search by the mathematical structure of the statement before accepting a new declaration (recon owns the search procedure). A lemma re-proved from scratch when Mathlib already carries it wastes a review round: the duplicate is closed, not merged.

### Generality and robustness probes

Probe, do not assume. When an argument is uniform in a parameter (for example every positive degree), a fixed-case statement is a scope defect: generalize the statement and see whether the proof still compiles, and require the uniform version. Perturb a proof to test robustness: change a hypothesis, rename a lemma, or move a definition, and rebuild; a proof that breaks on such a change rests on an implementation accident (a specific eliminator shape, hidden definitional equality, an unfolding-heavy `simpa`) and needs an explicit lemma or comment. A short-but-brittle proof is not a good proof.

## Pointer section

- TauCetiProject/TauCetiReview/rubrics/: the universal and per-change rubrics, and `_common.md` with the shared protocol (untrusted input, adversarial author, contested findings).
- TauCeti COORDINATION.md: the agent coordination contract the review protocol follows (Section 2: reading review state, head-bound verdicts).
- REVIEWING.md in TauCetiReview: how the rubric review is run, locally or by CI.
- leanprover-community.github.io/contribute: mathlib naming, style, and contribution documentation.
- For the golf-side discipline this review side checks, see the ut-lean-golf skill.
