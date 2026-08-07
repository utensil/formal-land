# Slice Design Checklist

## 1. Compact design check (five questions)

| Question | Answer |
| --- | --- |
| 1. Dependency and scope: which authoritative requirement does this discharge, and what later declaration consumes it? | |
| 2. Natural statement: which variables and indices are genuinely arbitrary? | |
| 3. Existing structure: which pinned library map, equivalence, or composition theorem is the starting point? | |
| 4. Public behavioral contract: which consumer equations must work without unfolding? | |
| 5. Proof shape: which named map or composition theorem replaces the elementwise chain? | |

## 2. Ten-gate slice-selection rubric

| Gate | Required evidence | Fail condition |
| --- | --- | --- |
| Exact target | A named declaration or theorem family | The goal is only a topic |
| Existing-library boundary | The objects to reuse and the missing theorem are listed | Re-proves an existing construction or duplicates an open pull request |
| Dependency depth | At most one or two unlanded prerequisites | The proof starts below several unresolved interfaces |
| One new idea | The central lemma states in one sentence | Combines several structures, actions, and irreducibility claims |
| Small instance | One low-dimensional or finite example exercises the route | Only the fully general theorem is specified |
| Reusable output | The general theorem is useful beyond the example | The result is an isolated computation |
| Acceptance oracle | Build, no-sorry policy, and a named test theorem are fixed | "It should compile" is the only validation plan |
| Convention lock | Signature, normalization, basis order, action, and operand order are explicit | The target depends on informal convention matching |
| Stop condition | A useful result exists if the generalization is abandoned | The work is all-or-nothing |
| Timebox | A short reconnaissance spike has a concrete end | Feasibility is inferred only from the specification |

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
