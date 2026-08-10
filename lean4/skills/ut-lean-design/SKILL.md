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

1. **Dependency and scope.** Which authoritative requirement does the slice
   discharge? What declaration consumes it? Why is the boundary coherent?
2. **Natural statement.** Which variables are genuinely arbitrary? Link the
   recon hypothesis probes by declaration name and result. Before accepting
   finiteness for an equivalence, try an explicit inverse or extensionality
   route.
3. **Existing structure.** Which pinned map, equivalence, or composition
   theorem is the starting point? Link the recon evidence.
4. **Public consumer contract.** Name each scratch consumer declaration and
   record whether it compiled. Cover the applicable application, membership,
   forward/inverse, zero/successor, and canonical-coordinate equations with
   opaque definitions and bare `simp` or an explicitly named theorem.
5. **Proof boundary.** Which named map or boundary lemma replaces an
   elementwise chain or private-construction definitional equality? Public
   proofs must not rely on unexplained `change`, `show`, or bare `rfl` across
   that boundary.

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
