---
name: ut-lean-review
description: Review for Lean and math formalization pull requests. The latest Tau Ceti rubrics are the default quality gate; the review process follows Tau Ceti coordination unless the project specifies its own rules. This skill is the extension layer on top: what the rubric wording does not say, learned from actual reviews.
---

# ut-lean-review

## Purpose

The default quality gate for math formalization is the Tau Ceti review rubrics (TauCetiProject/TauCetiReview): every formalization change is first reviewed against the latest universal and per-change rubrics, whatever repository it lives in. The review process follows Tau Ceti coordination (COORDINATION.md) whenever applicable, unless the project under review specifies its own review-process rules, which take precedence.

This skill does not restate any of that. It is an extension layer: every section below names the rubric or coordination rule it extends, records what we learned in actual reviews that the rule's general wording does not say, and marks what cannot be missed. Anything the rubrics, coordination, or CI already carry is only referenced.

## How the layers stack

1. The project's own review-process rules, when it specifies them.
2. The latest Tau Ceti rubrics: the default quality gate for all formalization.
3. Tau Ceti coordination for the review process, when applicable.
4. The extensions in this skill.

Do not re-report what CI or the linters already enforce: the build, the axiom audit, the Mathlib linter set, and the import boundary are checked mechanically, and the rubric agents do not re-check them either.

## What you cannot miss

- A review binds to one exact head; a new commit requires a fresh review.
- Inspect the aggregate diff, not the latest commit: a change introduced several commits back can hide behind it.
- A fixed-case statement of a uniform argument is a scope defect even when the proof is correct.
- A duplicate in disguise is still duplication: same content up to definitional spelling, symmetry, or duality.
- A docstring that overclaims hides a real dependency.
- A proof that breaks when a nearby definition moves rests on an implementation accident.

## Review process extensions

### Extends COORDINATION.md Section 2: head-bound verdicts

The rule: a review applies only to the head commit it names; a new commit needs a fresh review. The extension from our reviews: when the PR accumulated several commits, compare against the aggregate diff rather than trusting the latest commit alone, and classify each finding as blocking, nonblocking, or optional. Never convert an unperformed check into a pass.

### Extends COORDINATION.md Section 2: the post-revision recheck

A revision is a new head, hence a new review. What we learned to recheck every time: the old and new public declarations, the consumers of moved or renamed names, direct imports with targeted builds, the complete build, the exact aggregate diff, and the remote branch state.

### Extends `_common.md`: contested findings

The rubric protocol for a contested finding is to engage the quote: restate compatibly, withdraw, or let it stand. What we learned around it:

- Keep an implement, contest, or wait ledger with one entry per finding, bound to an exact head.
- The compiler and the linter are the arbiter. Contest a wrong prescription with a pinned probe (a deletion probe, the full linter output), not by a repair loop that mutates the code hoping the finding stops firing. A contest replies to the exact review comment that raised the finding, names the exact head and the compiler evidence, and reproduces the full lint result locally first. Keep a named non-simp theorem rather than adding a lint exception, for example a requested `@[simp]` that the `simpNF` normal form already reduces.
- Combine interacting requests into one candidate; alternating fix and revert commits makes a finding impossible to verify.
- Respond proportionally: an API-surface change runs the full gate; a small delimited repair runs a focused build, the affected consumer probes, and a diff-scoped review; a source-equivalent rebase or message-only rewrite verifies byte-identical source and history rather than re-running mathematical review. The failure mode we hit: re-running the entire gate ceremony for a handful of changed lines.

## Quality extensions, one per rubric

### Extends reuse.md: search before writing

reuse.md specifies the search protocol and the defects to detect. The lesson from our reviews: a duplicate discovered at review time (for example a proof re-deriving a declaration Mathlib already carries) wastes a whole round; the search belongs before writing, and ut-lean-recon owns the procedure. Run it before the declaration exists, not after the reviewer finds it.

### Extends generality.md: uniform arguments stated uniformly

generality.md requires the natural level and general-first. The concrete failure mode we hit: a construction fixed at one degree although the argument is uniform in every degree, re-scoped into the all-degree version. The probe: generalize the statement and recompile; if the proof survives, the fixed-case statement is a scope defect.

### Extends proof-quality.md: robustness probes

proof-quality.md flags brittle proofs and undocumented definitional equality. The detection technique: perturb and rebuild. Change a hypothesis, rename a lemma, or move a definition; a proof that breaks on such a change rests on an implementation accident (a specific eliminator shape, an unfolding-heavy `simpa`, a hidden defeq) and needs an explicit lemma or comment. A short-but-brittle proof is not a good proof.

### Extends documentation.md: docstring-hypothesis traps

documentation.md treats overclaiming as a finding even when the theorem is correct. The concrete traps we keep seeing: calling an arbitrary element central, an endomorphism a projection before idempotence is proved, or a construction canonical when it depends on selected data. Overclaimed docstrings are how a review misses a real dependency.

### Extends naming.md: name against the next model

naming.md requires conclusion-describing names and adjacent consistency. The extension: test public names against known future constructions, not only the current file. An equivalence named for its current source became ambiguous when a second natural equivalence for the same objects was planned; the role-based name, recording the direction it establishes, left room for the later bridge.

### Extends placement.md: probe imports instead of guessing

placement.md reports only evidently wrong imports and leaves the mechanical boundary to CI and `shake`. When imports are suspect, decide with removal probes and small import-only compile probes rather than by guessing from the current build, and watch for a generic module importing a later specialization.

## Checks the rubrics do not carry

General Lean structural additions, not extensions of any single rubric:

- Separate the stack from the change: record both the GitHub-visible diff against the integration branch and the change's own diff against its integration base. The first determines the human dependency order; the second whether the change is structurally too large. Do not split a coherent change merely because GitHub includes prerequisite files.
- Organize around downstream consumers: two groups of declarations deserve separate modules when later work needs one without the other. Before a split, ask whether it removes a real dependency for a planned consumer, whether each module has a stable mathematical responsibility, whether the higher layer can import the lower one without a cycle, and whether the split would remain sensible if this PR did not exist.
- Roots and aggregators as policy: an import-free root avoids a transitive catch-all; a feature PR must not turn it into a rolling re-export, and aggregators need an explicit ownership and import contract rather than arising from whichever feature touched the root last.

## Pointer section

- TauCetiProject/TauCetiReview/rubrics/: the latest universal and per-change rubrics (the default gate); `_common.md` holds the shared protocol (untrusted input, adversarial author, contested findings).
- TauCeti COORDINATION.md: the coordination contract the review process follows by default (Section 2: reading review state, head-bound verdicts); project-specified review-process rules take precedence.
- REVIEWING.md in TauCetiReview: how the rubric review is run, locally or by CI.
- leanprover-community.github.io/contribute: mathlib naming, style, and contribution documentation.
- ut-lean-recon: the search procedure reuse extensions point to; ut-lean-golf: the proof-golf discipline this review side checks.
