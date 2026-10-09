---
name: ut-lean-design
description: Pre-source design for one Lean slice. Fixes the exact target, natural statement, reused structure, public consumer contract, and proof boundary against compiled probes.
---

# ut-lean-design

Design turns one `ut-lean-roadmap` milestone and one `ut-lean-recon` manifest
into a reviewable public contract. If a design choice raises a new API or
hypothesis question, run a focused recon probe and update the manifest.

## Use it

- before the first source edit of a new slice;
- when a candidate lacks a named consumer, convention test, or proof boundary;
- when review shows that the current contract is incomplete.

## Five questions

1. **Dependency and scope.** Which authoritative requirement does this slice address, and why is it a coherent unit? Trace its prerequisites and first downstream use; distinguish inseparable support from independently reusable results.

2. **Natural statement.** Which variables are arbitrary, and which hypotheses does the mathematics need? Compare nearby statements and recon probes; weakening assumptions, or trying an explicit inverse or extensionality for an equivalence, can reveal the natural generality.

3. **Existing structure.** Which existing map, equivalence, universal property, or composition theorem offers a starting point? Search the pinned library by structure and conclusion, then try the candidate’s actual signature in a small recon probe.

4. **Public consumer contract.** What should the immediate downstream declaration be able to state and prove through this API? Try its actual signature and first use in a compiled scratch consumer without unfolding definitions. Representative application, membership, inverse, recursion, or coordinate equations can reveal missing laws; for an operation paired with a relation, what makes them coherent?

5. **Proof boundary.** Which map or lemma should connect the chosen construction to its downstream proofs? Test the existing API in a small consumer; if presentations differ, `change` or a local `rfl` equality can help reveal the needed comparison. Is that comparison specific to this proof, or useful enough to expose as a reusable lemma?

## Locks and exit

- Pin signs, scalar factors, directions, and normalizations with small compiled
  equalities before generalizing.
- Treat the narrative specification as authoritative; target stubs may be
  non-exhaustive.
- For each public definition, provide the characteristic application or
  membership equations. Let lint determine `@[simp]` orientation; use
  `@[expose]` only when a real consumer must unfold.
- Keep inseparable support with its immediate consumer and split independent
  reusable work.
- Stop when the selected consumer contract passes. Record the exact probe
  names and results in `CHECKLIST.md` for implementation and review.

## References

- Selection: `ut-lean-roadmap`
- Evidence: `ut-lean-recon`
- Implementation checks: `ut-lean-golf`, `ut-lean-review`
- Review rubrics: <https://github.com/TauCetiProject/TauCetiReview/rubrics/>
- Handoff record: `CHECKLIST.md`
