---
name: ut-lean-review
description: 'Review for Lean and math formalization pull requests. The latest Tau Ceti rubrics are the default quality gate; the review process follows Tau Ceti coordination unless the project specifies its own rules. This skill is the extension layer on top: what the rubric wording does not say, learned from actual reviews.'
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

Read [RUBRICS.md](RUBRICS.md) before starting a review. It is the required-id
registry for both the Tau Ceti rubrics and this skill's extensions.

Do not re-report what CI or the linters already enforce: the build, the axiom audit, the Mathlib linter set, and the import boundary are checked mechanically, and the rubric agents do not re-check them either.

## What you cannot miss

- A review binds to one exact head; a new commit requires a fresh review.
- Inspect the aggregate diff, not the latest commit: a change introduced several commits back can hide behind it.
- A fixed-case statement of a uniform argument is a scope defect even when the proof is correct.
- A duplicate in disguise is still duplication: same content up to definitional spelling, symmetry, or duality.
- A docstring that overclaims hides a real dependency.
- A proof that breaks when a nearby definition moves rests on an implementation accident.

## Review process extensions

### `ut-review-head-binding`: extends COORDINATION.md Section 2

The rule: a review applies only to the head commit it names; a new commit needs a fresh review. The extension from our reviews: when the PR accumulated several commits, compare against the aggregate diff rather than trusting the latest commit alone, and classify each finding as blocking, nonblocking, or optional. Never convert an unperformed check into a pass.

### `ut-review-revision`: extends COORDINATION.md Section 2

A revision is a new head, hence a new review. Recheck the old and new public declarations, consumers of moved or renamed names, direct imports, the exact aggregate diff, and the remote branch state. Scale execution to the change: use the complete build for an API-surface or final candidate, focused builds and affected probes for a delimited repair, and byte-identical source/history verification for a source-equivalent rebase.

If a finding changes prerequisite order, minimal hypotheses, construction strategy, the exported API, or module ownership, classify it as architectural. Stop the local repair cycle, return the slice to reconnaissance and design, and invalidate dependent provisional reviews until their consumer probes pass against the revised contract. After a material repair, review the full aggregate proof surface again rather than only the named findings.

### `ut-review-contest`: extends `_common.md`

The rubric protocol for a contested finding is to engage the quote: restate compatibly, withdraw, or let it stand. What we learned around it:

- Keep an implement, contest, or wait ledger with one entry per finding, bound to an exact head.
- The compiler and the linter are the arbiter. Contest a wrong prescription with a pinned probe (a deletion probe, the full linter output), not by a repair loop that mutates the code hoping the finding stops firing. A contest replies to the exact review comment that raised the finding, names the exact head and the compiler evidence, and reproduces the full lint result locally first. Keep a named non-simp theorem rather than adding a lint exception, for example a requested `@[simp]` that the `simpNF` normal form already reduces.
- Combine interacting requests into one candidate; alternating fix and revert commits makes a finding impossible to verify.
- If the same logical finding needs a second revision, stop before another public write and reread the whole thread, the previous variants, and the intended consumer contract. Replace comment-by-comment interpretation with one stable combined candidate.
- Respond proportionally: an API-surface change runs the full gate; a small delimited repair runs a focused build, the affected consumer probes, and a diff-scoped review; a source-equivalent rebase or message-only rewrite verifies byte-identical source and history rather than re-running mathematical review. The failure mode we hit: re-running the entire gate ceremony for a handful of changed lines.

## Quality extensions, one per rubric

### `ut-reuse-search-before-writing`: extends reuse.md

reuse.md specifies the search protocol and the defects to detect. The lesson from our reviews: a duplicate discovered at review time (for example a proof re-deriving a declaration Mathlib already carries) wastes a whole round; the search belongs before writing, and ut-lean-recon owns the procedure. Run it before the declaration exists, not after the reviewer finds it.

### `ut-generality-uniformity`: extends generality.md

generality.md requires the natural level and general-first. The concrete failure mode we hit: a construction fixed at one degree although the argument is uniform in every degree, re-scoped into the all-degree version. The probe: generalize the statement and recompile; if the proof survives, the fixed-case statement is a scope defect.

### `ut-proof-robustness`: extends proof-quality.md

proof-quality.md flags brittle proofs and undocumented definitional equality. The detection technique: perturb and rebuild. Change a hypothesis, rename a lemma, or move a definition; a proof that breaks on such a change rests on an implementation accident (a specific eliminator shape, an unfolding-heavy `simpa`, a hidden defeq) and needs an explicit lemma or comment. A short-but-brittle proof is not a good proof.

Scan every public proof in the aggregate diff for `change`, `show`, and bare `rfl` across private definitions or equivalences. A public theorem needs an explicit application or conversion lemma at that boundary; documenting the reshaping does not make the consumer contract robust.

### `ut-documentation-dependency-claims`: extends documentation.md

documentation.md treats overclaiming as a finding even when the theorem is correct. The concrete traps we keep seeing: calling an arbitrary element central, an endomorphism a projection before idempotence is proved, or a construction canonical when it depends on selected data. Overclaimed docstrings are how a review misses a real dependency.

### `ut-naming-future-models`: extends naming.md

naming.md requires conclusion-describing names and adjacent consistency. The extension: test public names against known future constructions, not only the current file. An equivalence named for its current source became ambiguous when a second natural equivalence for the same objects was planned; the role-based name, recording the direction it establishes, left room for the later bridge.

### `ut-placement-import-probes`: extends placement.md

placement.md reports only evidently wrong imports and leaves the mechanical boundary to CI and `shake`. When imports are suspect, decide with removal probes and small import-only compile probes rather than by guessing from the current build, and watch for a generic module importing a later specialization.

## `ut-structural-boundaries`: checks the rubrics do not carry

General Lean structural additions, not extensions of any single rubric:

- Separate the stack from the change: record both the GitHub-visible diff against the integration branch and the change's own diff against its integration base. The first determines the human dependency order; the second whether the change is structurally too large. Do not split a coherent change merely because GitHub includes prerequisite files.
- Organize around downstream consumers: two groups of declarations deserve separate modules when later work needs one without the other. Before a split, ask whether it removes a real dependency for a planned consumer, whether each module has a stable mathematical responsibility, whether the higher layer can import the lower one without a cycle, and whether the split would remain sensible if this PR did not exist.
- Roots and aggregators as policy: an import-free root avoids a transitive catch-all; a feature PR must not turn it into a rolling re-export, and aggregators need an explicit ownership and import contract rather than arising from whichever feature touched the root last.

## Evidence gate

Write the independent review as an internal review scoreboard in Markdown using
[templates/review-evidence.md](templates/review-evidence.md). Keep one scoreboard
row per required rubric id with four fields: rubric id, verdict, evidence, and
comment. Use Tau Ceti's verdict vocabulary: `approve`, `request_changes`, or
`block`.

Run the bundled validator before accepting a review:

```bash
python3 scripts/validate-review-evidence.py /path/to/review.md
```

The validator fails on a missing, duplicate, or unknown rubric id; a missing
verdict, evidence, or comment; or any verdict other than `approve`. A complete
`request_changes` review remains useful evidence, but it does not pass the
private approval gate. After repairing source, create a fresh exact-head review
and validate it again. Never infer an omitted rubric's verdict from prose.

## Pointer section

- TauCetiProject/TauCetiReview/rubrics/: the latest universal and per-change rubrics (the default gate); `_common.md` holds the shared protocol (untrusted input, adversarial author, contested findings).
- TauCeti COORDINATION.md: the coordination contract the review process follows by default (Section 2: reading review state, head-bound verdicts); project-specified review-process rules take precedence.
- REVIEWING.md in TauCetiReview: how the rubric review is run, locally or by CI.
- leanprover-community.github.io/contribute: mathlib naming, style, and contribution documentation.
- ut-lean-recon: the search procedure reuse extensions point to; ut-lean-golf: the proof-golf discipline this review side checks.
