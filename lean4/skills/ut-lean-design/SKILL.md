---
name: ut-lean-design
description: Design of a Lean formalization slice before writing any code. Applies the five-question compact design check, the smallest-instance algorithm, the ten-gate slice-selection rubric, convention locks by definitional acceptance tests, and the characteristic-API rules for public declarations.
---

# ut-lean-design

## Purpose

A formalization slice is one coherent unit of Lean work: one topic, one pull request, one reviewable contract. Design is the step that fixes the slice before any code is written. It picks the exact target, the natural statement, the library boundary, the public behavioral contract, and the proof shape, and it pins conventions with small concrete tests. Design consumes the verdict from ut-lean-recon and produces a checklist that the implementation must pass.

## When to use

- Before the first edit of any new slice.
- When selecting the next slice from a roadmap or backlog.
- When a candidate has no named target, no consumer, or no convention test.
- During review, to check a candidate against its design contract.

## Procedure

### 1. Run the compact design check

Record answers to these five questions before implementation:

1. Dependency and scope: which authoritative requirement does this slice discharge, what later declaration consumes it, and why is it one coherent slice rather than a fixed-degree or partial copy?
2. Natural statement: which variables and indices are genuinely arbitrary? If the proof works uniformly in a degree, a form, or a module, state it that way unless a real dependency prevents it.
3. Existing structure: which pinned library map, equivalence, or composition theorem is the natural starting point? Search by the mathematical structure, not only by a hoped-for theorem name.
4. Public behavioral contract: for every public definition or equivalence, which consumer equations must work without unfolding it? Test a small downstream import and a bare `simp`, both directions when an equivalence is exposed.
5. Proof shape: can a named map or composition theorem replace an elementwise equality chain, an ad hoc wrapper, or a carrier-level transition? Keep an essential `change` only with a local explanation.

### 2. Run the operational algorithm

1. Search the repository and open pull requests before selecting the target.
2. Read the exact library declarations the proof will consume.
3. Write the smallest concrete instance and its expected normal form.
4. Test the instance without building the general abstraction.
5. Extract the one reusable theorem exposed by that test.
6. Land the theorem and the instance as separate, reviewable milestones when the boundary is real.
7. Stop or expand only after the acceptance oracle passes.

### 3. Score the slice against the ten gates

Score each candidate before implementation (the full table with evidence and fail conditions is in CHECKLIST.md):

1. Exact target: a named declaration or theorem family.
2. Existing-library boundary: the objects to reuse and the missing theorem are listed.
3. Dependency depth: at most one or two unlanded prerequisites.
4. One new idea: the central lemma states in one sentence.
5. Small instance: one low-dimensional or finite example exercises the route.
6. Reusable output: the general theorem is useful beyond the example.
7. Acceptance oracle: build, no-sorry policy, and a named test theorem are fixed.
8. Convention lock: signature, normalization, basis order, action, and operand order are explicit.
9. Stop condition: a useful result exists if the generalization is abandoned.
10. Timebox: a short reconnaissance spike has a concrete end.

Review rubrics are a separate concern from slice selection. When the slice is under review, use the project's rubric index at TauCetiProject/TauCetiReview/rubrics/ rather than restating it in the design.

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

### 7. Land one topic per milestone

One pull request, one idea, one reviewable boundary. Ship a prerequisite refactor as its own milestone. Stop when the acceptance oracle passes.

## References

- The reconnaissance companion skill: ut-lean-recon
- The companion golf and review skills: ut-lean-golf, ut-lean-review
- The Lean theorem prover manual: <https://lean-lang.org/theorem_proving_in_lean4/>
- Review rubrics (used at review time, not slice selection): <https://github.com/TauCetiProject/TauCetiReview/rubrics/>
- Checklist templates: CHECKLIST.md
