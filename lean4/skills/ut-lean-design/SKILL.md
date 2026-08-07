---
name: ut-lean-design
description: Design of a Lean formalization work unit before writing any code: the five-question compact design check, convention locks by definitional acceptance tests, the authoritative-spec principle, and the characteristic-API rules for public declarations. Slice selection (the gates and the operational algorithm) is ut-lean-roadmap's concern.
---

# ut-lean-design

## Purpose

Design operates at the level of a single work unit: one topic, one reviewable contract, which may map to a pull request. It fixes the unit before any code is written: the exact target, the natural statement, the library boundary, the public behavioral contract, and the proof shape, with conventions pinned by small concrete tests. The slice (the attack angle), the route (the plan), and the work unit (the concrete deliverable) are defined in ut-lean-roadmap; design takes one work unit as its input and produces a checklist the implementation must pass. Design consumes the verdict from ut-lean-recon.

## When to use

- Before the first edit of any new work unit.
- When selecting the next work unit from a roadmap or backlog.
- When a candidate has no named target, no consumer, or no convention test.
- During review, to check a candidate against its design contract.

## Procedure

### 1. Run the compact design check

Record answers to these five questions before implementation:

1. Dependency and scope: which authoritative requirement does this work unit discharge, what later declaration consumes it, and why is it one coherent work unit rather than a fixed-degree or partial copy?
2. Natural statement: which variables and indices are genuinely arbitrary? If the proof works uniformly in a degree, a form, or a module, state it that way unless a real dependency prevents it.
3. Existing structure: which pinned library map, equivalence, or composition theorem is the natural starting point? Search by the mathematical structure, not only by a hoped-for theorem name.
4. Public behavioral contract: for every public definition or equivalence, which consumer equations must work without unfolding it? Test a small downstream import and a bare `simp`, both directions when an equivalence is exposed.
5. Proof shape: can a named map or composition theorem replace an elementwise equality chain, an ad hoc wrapper, or a carrier-level transition? Keep an essential `change` only with a local explanation.

### 2. Selection comes first

Run slice selection before design: the gates and the operational algorithm (concrete probe, general theorem as the deliverable, acceptance oracle) live in ut-lean-roadmap. Design consumes its verdict. The probe is concrete; the deliverable is the general theorem the probe supports.

### 3. Score the work unit against the gates

The slice-selection gates (exact target, existing-library boundary, dependency depth, one new idea, concrete probe, reusable output, acceptance oracle, convention lock, stop condition, timebox) are owned by ut-lean-roadmap; score the candidate there before designing. The authoritative table with evidence and fail conditions is ut-lean-roadmap/ROUTES.md. The deliverable is always the general theorem; a concrete probe only exercises the route.

### 4. Lock conventions by definitional acceptance tests

Before generalizing, pin the signature and the normalization with small concrete tests that compile. Examples: fix a signature convention with four base-entry tests; pin a bivector normalization by proving its defining action identity against the library's polar convention. Do not fix a scalar factor (such as a factor of one half) before the convention is pinned. A convention test is a compile-checked equality, not a prose statement.

### 5. Treat the authoritative specification as definitive

The human-maintained narrative specification is definitive for scope and completion. A sorry-target stub file is explicitly non-exhaustive: matching its signatures cannot establish that a layer or prerequisite is complete. Scope contests need narrative-specification evidence, not stub-file signatures.

### 6. Apply the characteristic-API rules

Ship with every public definition:

- `mem_*_iff` and apply equations, plus forward and inverse computation equations for equivalences;
- `@[simp]` orientation decided by the linter (run it; the reverse `_mk` orientation is the normal form);
- `@[expose]` only when a concrete consumer must unfold the definition and no computation lemma covers it;
- names that describe conclusions;
- shared definitions placed in the earliest file that uses them.

### 7. Land one topic per work unit

One work unit, one idea, one reviewable boundary (the unit may map to a pull request). Ship a prerequisite refactor as its own unit. Stop when the acceptance oracle passes.

## References

- The reconnaissance companion skill: ut-lean-recon
- The definitions and slice-selection owner: ut-lean-roadmap (layer, slice, route, work unit; gates; operational algorithm)
- The companion golf and review skills: ut-lean-golf, ut-lean-review
- The Lean theorem prover manual: <https://lean-lang.org/theorem_proving_in_lean4/>
- Review rubrics (used at review time, not unit selection): <https://github.com/TauCetiProject/TauCetiReview/rubrics/>
- Checklist templates: CHECKLIST.md
