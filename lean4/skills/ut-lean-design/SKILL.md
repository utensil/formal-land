---
name: ut-lean-design
description: Design of a Lean formalization slice before writing any code: the five-question compact design check, convention locks by definitional acceptance tests, the authoritative-spec principle, and the characteristic-API rules for public declarations. Slice selection is ut-lean-roadmap's concern.
---

# ut-lean-design

## Purpose

Design operates at the level of a single slice: one topic, one reviewable contract, which may map to a pull request. It fixes the slice before any code is written: the exact target, the natural statement, the library boundary, the public behavioral contract, and the proof shape, with conventions pinned by small concrete tests. The roadmap, layer, route, and slice are defined in ut-lean-roadmap; design takes one selected slice as its input and produces a checklist the implementation must pass. Design consumes the verdict from ut-lean-recon, the main direction being recon before design; when a design decision raises a new API question (a convention to pin, a signature shape, a library boundary), run a focused recon probe against the pinned revision instead of guessing, and iterate until the contracts are pinned.

## When to use

- Before the first edit of any new slice.
- When selecting the next slice from a roadmap or backlog.
- When a candidate has no named target, no consumer, or no convention test.
- During review, to check a candidate against its design contract.

## Procedure

### 1. Run the compact design check

Record answers to these five questions before implementation:

1. Dependency and scope: which authoritative requirement does this slice discharge, what later declaration consumes it, and why is it one coherent slice rather than a fixed-degree or partial copy?
2. Natural statement: which variables and indices are genuinely arbitrary? Compile deletion probes for nontrivial hypotheses. If an equivalence currently needs finiteness only to obtain bijectivity, try an explicit inverse or generator-extensionality route before accepting that assumption.
3. Existing structure: which pinned library map, equivalence, or composition theorem is the natural starting point? Search by the mathematical structure, not only by a hoped-for theorem name.
4. Public behavioral contract: for every public definition or equivalence, inventory the application, membership, forward, inverse, and canonical-coordinate equations that its first real consumer needs. Test each relevant direction in a small downstream import with the definition kept opaque and bare `simp` where appropriate.
5. Proof shape: can a named map or composition theorem replace an elementwise equality chain, an ad hoc wrapper, or a carrier-level transition? A public theorem that crosses a private construction by `change`, `show`, or bare `rfl` needs an explicit boundary lemma; a comment alone is not the API.

### 2. Confirm selection

Run `ut-lean-roadmap` first. Design consumes its selected milestone, summit,
prerequisite closure, downstream consumer, and natural-generality decision.
If design invalidates one of them, return to selection rather than silently
changing the route.

### 3. Lock conventions by definitional acceptance tests

Before generalizing, pin the signature and the normalization with small concrete tests that compile. Examples: fix a signature convention with four base-entry tests; pin a bivector normalization by proving its defining action identity against the library's polar convention. Do not fix a scalar factor (such as a factor of one half) before the convention is pinned. A convention test is a compile-checked equality, not a prose statement.

### 4. Treat the authoritative specification as definitive

The human-maintained narrative specification is definitive for scope and completion. A sorry-target stub file is explicitly non-exhaustive: matching its signatures cannot establish that a layer or prerequisite is complete. Scope contests need narrative-specification evidence, not stub-file signatures.

### 5. Apply the characteristic-API rules

Ship with every public definition:

- `mem_*_iff` and apply equations, plus forward and inverse computation equations for equivalences;
- `@[simp]` orientation decided by the linter (run it; the reverse `_mk` orientation is the normal form);
- `@[expose]` only when a concrete consumer must unfold the definition and no computation lemma covers it;
- names that describe conclusions;
- shared definitions placed in the earliest file that uses them.

### 6. Preserve the slice boundary

Keep one coherent reviewable boundary. Include an inseparable supporting result
when the selected milestone immediately consumes it; split independent reusable
work. Stop when the selected consumer contract passes.

## References

- The reconnaissance companion skill: ut-lean-recon
- The definitions and slice-selection owner: ut-lean-roadmap
- The companion golf and review skills: ut-lean-golf, ut-lean-review
- The Lean theorem prover manual: <https://lean-lang.org/theorem_proving_in_lean4/>
- Review rubrics (used at review time, not unit selection): <https://github.com/TauCetiProject/TauCetiReview/rubrics/>
- Checklist templates: CHECKLIST.md
