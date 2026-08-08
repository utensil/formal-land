---
name: ut-lean-golf
description: Shorten Lean proofs at the mathematical interface by replacing locally rebuilt machinery with the library abstraction that already names the object. Survey the pinned revision, search by structure before writing lemmas, state at natural generality, extract shared criteria on first reuse, and land structural API at the project's permitted boundary before specializing.
---

# ut-lean-golf

## Purpose

Lean proof golf at the mathematical interface. A long proof is not itself a problem: it becomes a golf candidate when its length comes from rebuilding a standard universal construction, normal-form interface, bundled morphism, or decomposition that mathlib already names. The productive question is not which tactics shorten the proof. It is: what mathematical object is this proof constructing, and does mathlib already name that object?

The goal is not the smallest line count. It is to remove local machinery when a current mathlib abstraction states the same mathematics more directly, while preserving the intended theorem surface and making dependency ownership clearer.

## When to use

Use this skill when:

- a proof manually rebuilds machinery mathlib already names: a lift out of a cyclic quotient, a linear endomorphism from scalar multiplication, a quotient preimage, a bijectivity argument built from finite cardinality;
- the same proof shape appears a second time (the rule of two);
- a proof is fixed to one degree or one specialization while the argument is uniform across all of them;
- a reviewer flags a re-derivation of mathlib API.

Do not use it merely to shorten a proof. A proof that is long because it carries a concrete calculation may be correct as written. Keep calculations where they expose the mathematical content, and use structural interfaces for the consequences that should not repeat those calculations.

## Procedure

### 1. Ask the interface question first

Identify the mathematical object the proof constructs (homomorphism, equivalence, submodule, graded piece, quotient) and search mathlib for the declaration that already names it, before touching tactics.

### 2. Search by structure before writing any lemma

Grep the checked-out mathlib for the proof shape before writing a new lemma. Re-deriving mathlib API is the block-capable reuse failure this prevents. See the reference file for the search procedure.

### 3. Survey the pinned mathlib revision

The first survey is a pinned-source API survey: rg over the checked-out mathlib revision, inspection of current declarations and adjacent source in the relevant domain, small compile probes for candidate declarations, removal probes to determine direct imports, then targeted and full builds against the pinned revision.

### 4. Escalate to mathlib history only on triggers

A repository-history or pull-request survey is warranted when the expected abstraction is materially missing, several interfaces compete, the API is recent or deprecated or moving, an upstream contribution is being considered, a proof depends on an implementation accident, a public compatibility choice is material, or current source cannot explain an unusual design. A clear one-line local bridge does not trigger archaeology on its own. See the reference file for the complete list.

### 5. State at natural generality

If the proof works uniformly in a degree, state the theorem for all degrees instead of the one fixed degree the immediate need has. A generator argument that proves equality should not be stated as an inequality; a generic filtration theorem should not be wrapped for a single special form. Specialization is then a thin consumer, and the theorem surface is future-proof.

### 6. Extract on first reuse (rule of two)

Ship the criterion lemma with the pull request that first repeats the proof shape. When the second occurrence of a pattern appears, extract the shared lemma in that same pull request, so the third occurrence and every later one consume the API and reviewers do not re-litigate the shape.

### 7. Land structural API at the permitted boundary first

When the reusable piece is generic, land it at the earliest boundary the
project permits before the specialization. In a project that welcomes a
Mathlib contribution, that may be Mathlib first; in a project that keeps its
roadmap work local, it means a generic project-local declaration. Never infer
permission to open an upstream pull request from this skill. The invariant is
structural API before repeated specialization, not a particular repository.

### 8. Recheck the boundary after golf

Golf can silently alter public helper declarations, theorem hypotheses, reducibility or simplification behavior, public imports, and downstream availability. After every golf, recheck the boundary and rebuild. See the reference file.

## Worked idioms

Generic shapes worth recognizing in ordinary proofs:

- A manual bilinear build that proves the linearity fields by hand should be replaced by the bundled construction that already exists: Submodule.mulMap' for multiplying two submodules, TensorProduct.curry for currying a bilinear map, LinearMap.liftQ₂ for descending a bilinear map to quotients.
- Thin wrappers that merely restate an existing mathlib equation, such as DirectSum.of_mul_of or DirectSum.algebraMap_apply, should be deleted in favor of the original rather than wrapped.
- Never re-prove AlternatingMap facts: alternation, swap and self behavior, and the universal property live in LinearAlgebra.Alternating.
- The positive model for a reusable construction is a generic degree-indexed construction, one public defining equation, and one theorem stating its usefulness, for example surjectivity or the universal property. Ship those three together so consumers invoke the lemmas instead of re-deriving the construction.

## Failure modes

Two failure modes are worth recognizing in golfed proofs:

- A lemma re-proved from scratch when Mathlib already carries it wastes a review round: the duplicate is closed, not merged. Search by structure before writing the declaration (recon owns the search procedure).
- A construction fixed at one concrete degree although the argument is uniform in every degree must be re-scoped to the all-degree version. State the general theorem even when a concrete case satisfies the immediate need.

## References

- REFERENCE.md in this skill directory: the mathlib-history escalation triggers and the post-golf boundary recheck.
- The pinned-source survey procedure is owned by ut-lean-recon; run it before golfing.
- Mathlib source: leanprover-community/mathlib4.
- For the review-side checks that interact with golf, see the ut-lean-review skill.
