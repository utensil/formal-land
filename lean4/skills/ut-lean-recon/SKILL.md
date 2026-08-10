---
name: ut-lean-recon
description: Pinned-revision API reconnaissance before Lean design. Classifies requirements as direct, local lemma, or infrastructure blocker and records reusable APIs, minimal hypotheses, conventions, and collisions.
---

# ut-lean-recon

Recon determines what already exists at the project's exact revisions and what
work remains. It owns pinned API, reuse, hypothesis, convention, and
reachability evidence. Design consumes its verdict and manifest.

## Use it

- before proposing a theorem, instance, definition, or notation;
- when a plan relies on a remembered library name;
- when a new type or helper may duplicate an existing construction;
- when design, golf, or review exposes an unresolved API question.

## Procedure

1. **Pin the environment.** Record the project commit, Lean toolchain, pinned
   mathlib commit, and Lake-managed checkout path. Search that checkout, not
   current mathlib master. Use a local reference checkout only for targeted
   history questions.
2. **Search and read structurally.** Search by mathematical structure and
   types, then read each candidate's full statement, assumptions, namespace,
   and adjacent API. A name or docstring is not evidence.
3. **Probe the boundary.** Compile scratch probes outside the repository.
   Remove each nontrivial hypothesis. For equivalences, try construction and
   inverse routes. Exact-conclusion-search every proposed helper shape,
   including helpers intended to stay private.
4. **Classify each requirement.** Use `direct`, `local lemma`, or
   `infrastructure blocker`. If the target already exists, return `no-gap`
   rather than proposing a wrapper.
5. **Check context.** Search merged and open project work for collisions. For
   equality or transport claims, record map direction, forms, signs, and
   scalar factors before claiming the conventions match.
6. **Record evidence.** Give every claim one level: `compiled`,
   `spike-boundary`, `inspected API`, or `proposed`. Journal failed remembered
   names and the route that replaced them.
7. **Emit a verdict.** Return `direct`, `no-gap`, or `blocker` with the compact
   `MANIFEST.md`. Design links that manifest instead of repeating its probes.

A spike may use a named `sorry` boundary only to test interface shape; it is
not evidence that the postponed proof is easy.

## References

- Mathlib source: <https://github.com/leanprover-community/mathlib4>
- Lean theorem prover manual: <https://lean-lang.org/theorem_proving_in_lean4/>
- Consumers: `ut-lean-design`, `ut-lean-golf`, `ut-lean-review`
- Record format: `MANIFEST.md`
