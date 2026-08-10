# Slice Design Checklist

## 1. Compact design check (five questions)

| Question | Answer |
| --- | --- |
| 1. Dependency and scope: which authoritative requirement does this discharge, and what later declaration consumes it? | |
| 2. Natural statement: which variables and indices are genuinely arbitrary, and which hypotheses survive compiled deletion probes? | |
| 3. Existing structure: which pinned library map, equivalence, or composition theorem is the starting point? | |
| 4. Public behavioral contract: which application, membership, forward, inverse, and canonical-coordinate equations must work without unfolding? | |
| 5. Proof shape: which named map or explicit boundary lemma replaces the elementwise chain or private-construction defeq? | |

## 2. Selected slice (owned by ut-lean-roadmap)

- [ ] Named summit and milestone recorded.
- [ ] Stable prerequisite closure and downstream consumer recorded.
- [ ] Natural generality and coherent milestone boundary recorded.

## 3. Convention lock by definitional acceptance tests

| Convention item | Test declaration | Expected normal form | Pinned against |
| --- | --- | --- | --- |
| | | | |

Examples: a signature convention pinned by four base-entry tests; a bivector normalization pinned by its defining action identity against the library's polar convention.

## 4. Pre-edit checklist

- [ ] Search result recorded: repository, merged history, open pull requests, pinned library.
- [ ] Exact declarations read from the pinned checkout.
- [ ] A focused probe resolves each uncertain feasibility or convention question.
- [ ] Consumer probe written (downstream import plus bare `simp`) and passed.
- [ ] Every relevant forward, inverse, and canonical-coordinate consumer compiled with public imports and opaque definitions.
- [ ] Nontrivial hypotheses passed deletion/generalization probes; an equivalence did not inherit finiteness merely from the first bijectivity proof.
- [ ] Independent reusable work is split; inseparable supporting results stay with their immediate consumer.
- [ ] Characteristic-API rules applied: `mem_*_iff`, apply and computation equations, linter-decided `@[simp]` orientation, no unconditional `@[expose]`, conclusion-describing names, earliest-file placement.
- [ ] Specification check: the claim matches the authoritative narrative specification, not only a stub-file signature.
- [ ] Public proofs do not cross private constructions through unexplained `change`, `show`, or bare `rfl`; an explicit boundary lemma covers the transition.

## 5. Acceptance oracle

- [ ] `lake build` passes at the exact head.
- [ ] No `sorry`, `admit`, or newly introduced axioms.
- [ ] Linter set passes, including `simp` orientation checks.
- [ ] Named test theorem exercises the public contract without unfolding definitions.
