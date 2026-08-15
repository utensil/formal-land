---
name: ut-lean-recon
description: Pinned-revision API reconnaissance before proposing any Lean theorem. Classifies each requirement as direct, local lemma, or infrastructure blocker against the exact pinned mathlib commit, and emits a verdict plus a manifest instead of wrapper theorems.
---

# ut-lean-recon

## Purpose

Reconnaissance is the exploration step that runs before any Lean theorem is proposed. Given a target statement and the project's pinned mathlib revision, it answers one question: which parts of the target already exist, which can be built from what exists, and which need new infrastructure? The answer is a verdict plus a manifest. Design, golf, and review consume that output, so recon must be complete and reproducible before any plan depends on an interface. The main direction is recon before design; design may re-invoke recon in focused form (a probe against the pinned revision) when its convention locks or signature choices raise new API questions, and the two iterate until the design's contracts are pinned against recon evidence.

## When to use

- Before proposing or approving any theorem, instance, or notation.
- Whenever a plan references a mathlib name from memory.
- Whenever a source-level claim (a paper, a note, a textbook statement) must be checked against the library.
- As the first step of a formalization slice (see ut-lean-design and ut-lean-roadmap), of a proof golf, or of a review.
- Whenever a new type looks like a re-spelling of an existing one.

## Procedure

### 1. Record the exact revision

The pinned mathlib commit, the Lean toolchain, and the project commit are part of every claim. Grep the pinned checkout, not the live master, unless the survey explicitly covers mathlib pull-request history. Record the checkout path in the manifest. The pinned checkout is the project's Lake-managed mathlib under `.lake/packages/`; it is not re-cloned. Surveys that need mathlib source history read the local reference checkout, pulled once per slice (skills README, Reference repositories), never a fresh clone.

### 2. Search by structure, not by name

Grep the pinned checkout for the mathematical structure and the types involved (a group type, a quotient construction, a bilinear form, a contraction operation), not only for a hoped-for theorem name. Names and docstrings drift; structure does not. If the search finds a type that is a definitional re-spelling of an existing quotient or construction, unify with the existing type instead of adding a third spelling.

### 3. Read the exact declarations

For every candidate declaration, read the statement, assumptions, universe levels, and namespace. A name is not evidence. Record what the declaration actually states, including hidden typeclass assumptions.

### 4. Classify reachability

For each requirement of the target, record one of:

- direct: a suitable declaration is already present at the pinned revision;
- local lemma: the result can be built from present APIs without new general theory;
- infrastructure blocker: a reusable construction or equivalence must be established before the result can be stated honestly.

Build the source-role versus existing-declaration table in MANIFEST.md, one row per requirement, each row tied to the pinned revision.

### 5. Apply no-gap discipline

If a source-level definition is already covered by mathlib, the conclusion is a documented no-gap result, not a wrapper theorem. A wrapper that merely restates an existing declaration duplicates library work and is rejected in review. Record the covered boundary precisely: hypotheses, direction, conventions. If the difference from the library version is substantive (a different definition shape, a different convention), record that difference instead of papering over it.

### 6. Search for collisions

Before proposing anything new, search mathlib, the project's merged history, and its open pull requests for the same or adjacent declarations. A collision means contribute to or build on the existing work, not re-open it.

When an authoritative milestone names sibling endpoints, census that family and record shared machinery, its earliest natural owner, and each endpoint's first consumer.

### 7. Compare conventions before claiming equality

No equality is claimed until a convention table records, for each side: the direction of the map, the source and target forms, and the signs or scalar factors. A change-of-form map, a quotient identification, or a normalization constant must be matched explicitly. Record the table in the manifest.

### 8. Journal failed probes

Remembered names are unreliable. Every probe that fails is journaled with the wrong remembered name and the correct route. Plans must never depend on an invented interface; the journal is the evidence that they do not.

### 9. Label evidence levels

Every claim in the manifest carries one label:

- compiled: elaborated on the pinned toolchain;
- spike-boundary: elaborated with a named sorry boundary that states the exact obligation postponed;
- inspected API: read from the pinned source, not elaborated;
- proposed: intended, not yet checked.

### 10. Run disposable scratch probes

Probes live in a scratch directory outside every repository and are never committed. A cache-backed build imports the pinned library and elaborates the candidate signatures or the minimal concrete instance. A spike may use a named sorry boundary only to test interface shape; a successful elaboration is not evidence that the postponed theorem is easy.

### 11. Emit the verdict and manifest

The recon output is:

- direct: the target is usable as-is from the pinned library;
- no-gap: the source-level material is already covered; document the boundary and propose no wrapper theorem;
- blocker: the missing infrastructure is identified and named in the manifest.

Attach MANIFEST.md with the tables and journal, and hand the verdict to design, golf, or review.

## References

- The pinned mathlib checkout and its revision history: <https://github.com/leanprover-community/mathlib4>
- The Lean theorem prover manual: <https://lean-lang.org/theorem_proving_in_lean4/>
- The companion skills that consume recon verdicts: ut-lean-design, ut-lean-golf, ut-lean-review
- The manifest templates: MANIFEST.md
- The project's review rubrics (the boundary between recon evidence and review findings is settled there).
