# Slice Design Checklist

## 1. Compact design check (five questions)

| Question | Answer |
| --- | --- |
| 1. Dependency and scope: which authoritative requirement does this discharge, and what later declaration consumes it? | |
| 2. Natural statement: which variables and indices are genuinely arbitrary? | |
| 3. Existing structure: which pinned library map, equivalence, or composition theorem is the starting point? | |
| 4. Public behavioral contract: which consumer equations must work without unfolding? | |
| 5. Proof shape: which named map or composition theorem replaces the elementwise chain? | |

## 2. Slice-selection gates (owned by ut-lean-roadmap)

- [ ] The candidate was scored against the slice-selection gates (exact target, existing-library boundary, dependency depth, one new idea, concrete probe, reusable output, acceptance oracle, convention lock, stop condition, timebox).
- [ ] The authoritative gate table and operational algorithm were applied from ut-lean-roadmap/ROUTES.md; not restated here.
- [ ] The deliverable is the general theorem; any concrete probe is only a feasibility spike, never the deliverable.

## 3. Convention lock by definitional acceptance tests

| Convention item | Test declaration | Expected normal form | Pinned against |
| --- | --- | --- | --- |
| | | | |

Examples: a signature convention pinned by four base-entry tests; a bivector normalization pinned by its defining action identity against the library's polar convention.

## 4. Pre-edit checklist

- [ ] Search result recorded: repository, merged history, open pull requests, pinned library.
- [ ] Exact declarations read from the pinned checkout.
- [ ] Smallest concrete instance drafted with its expected normal form.
- [ ] Consumer probe written (downstream import plus bare `simp`) and passed.
- [ ] One reusable theorem extracted from the probe.
- [ ] Theorem and instance split into separate milestones when the boundary is real.
- [ ] Characteristic-API rules applied: `mem_*_iff`, apply and computation equations, linter-decided `@[simp]` orientation, no unconditional `@[expose]`, conclusion-describing names, earliest-file placement.
- [ ] Specification check: the claim matches the authoritative narrative specification, not only a stub-file signature.

## 5. Acceptance oracle

- [ ] `lake build` passes at the exact head.
- [ ] No `sorry`, `admit`, or newly introduced axioms.
- [ ] Linter set passes, including `simp` orientation checks.
- [ ] Named test theorem exercises the public contract without unfolding definitions.
