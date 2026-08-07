---
name: ut-lean-golf-reference
description: Reference for ut-lean-golf. The escalation triggers for a mathlib repository-history survey and the post-golf boundary recheck. The pinned-source survey itself belongs to ut-lean-recon.
---

# ut-lean-golf reference: escalation and recheck

## The pinned-source survey

The first survey of any golf or reuse question runs against the checked-out mathlib revision, not memory. The survey procedure itself (grep the pinned revision, inspect adjacent source, compile probes, removal probes, targeted and full builds, and the canonical-API caution) is owned by ut-lean-recon; run it before golfing. Golf adds the triggers and the boundary recheck below.

## Escalation to a mathlib history survey

Add a repository-history or pull-request survey when at least one of the following holds:

1. The expected abstraction is materially missing. A recurring pattern, substantial local proof, unclear design choice, or intended upstream contribution remains after the pinned-source search. A clear one-line local bridge does not trigger repository archaeology on its own.
2. Several current interfaces compete. Source inspection does not reveal which declaration is intended for new downstream use.
3. The API is recent, deprecated, or moving. Commit and pull-request context may reveal the migration direction and compatibility expectations.
4. An upstream contribution is being considered. Naming, namespace, theorem shape, and accepted generality require evidence from comparable reviews and, when appropriate, human discussion.
5. A proof depends on an implementation accident. The current source compiles, but the public contract or stability of the behavior is unclear.
6. A public compatibility choice is material. Removing declarations, changing imports, or replacing a bundled construction may affect users beyond the current unmerged branch.
7. Current source cannot explain an unusual design. History may show a rejected alternative, performance constraint, elaboration issue, or contributor convention that is invisible in the final file.

Begin with the pinned-source survey, then escalate as soon as a trigger is met. An upstream proposal always requires that escalation and a separate human decision before public discussion or implementation.

## Post-golf boundary recheck

Proof golf can silently alter:

- public helper declarations;
- theorem hypotheses;
- reducibility or simplification behavior;
- public imports;
- downstream source availability.

Fresh independent review after a golf therefore compares exact heads, inspects the full aggregate diff, rebuilds targeted and repository targets, checks source claims, and audits the resulting commits and remote state.

## Calculation versus structure

Keep concrete calculations where they expose the mathematical content. Use structural interfaces for the consequences that should not repeat those calculations. A carrier theorem may still perform a finite case calculation, while a group equivalence should use a generator-and-cardinality interface. Explicit projection equations should remain visible even when bundled endomorphism and complementary-submodule APIs carry their structural consequences.

Treat simp volume as a symptom, not a metric. Large simp blocks can indicate that the proof is working below the intended abstraction, but replacing them mechanically is not an objective. A short proof is better only when its invoked theorem accurately communicates the mathematics and has stable hypotheses.

## Transported structures

Transported equivalences can determine dependent structures, for example a semidirect-product action, without remaining definitionally equal across module boundaries. Do not make later proofs depend on unfolding those constructors. Expose pointwise application lemmas and, when several transports are composed, name the intermediate model equivalence. This keeps the dependency visible and gives rewriting a stable proposition rather than an implementation detail.
