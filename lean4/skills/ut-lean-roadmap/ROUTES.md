# ROUTES.md: work-unit checklist

Run this before committing to a roadmap work unit. It is the executable form of the skill's methodology; it does not restate the prose in SKILL.md.

## Unit selection

- [ ] Named target in the roadmap, not a topic.
- [ ] One idea: the central lemma fits in one sentence; a prerequisite refactor is its own unit.
- [ ] General theorem is the deliverable; any concrete spike is only a probe.
- [ ] Natural generality: uniform arguments stated for all degrees or structures.
- [ ] Clear dependencies: at most one or two unlanded prerequisites; library objects to reuse listed.
- [ ] Named downstream consumer.
- [ ] Dependency value: an unmet prerequisite beats non-enabling nearby work; no scope stretch.
- [ ] Collision scan: no duplicate of an open contribution or claim.
- [ ] Boundary: no unapproved crossing into another work area.
- [ ] Convention lock: signature, normalization, direction, operand order explicit, pinned by definitional tests where the subject admits them.
- [ ] Acceptance oracle: build, no-sorry and axiom policy, named test theorem fixed.
- [ ] Stop condition and timebox: a useful result exists if the generalization is abandoned; the spike has an end.

## The gate table

| Gate | Required evidence | Fail condition |
| --- | --- | --- |
| Exact target | Named declaration, theorem family, or milestone in the roadmap | The goal is only a topic |
| Existing-library boundary | Library objects to reuse and the missing theorem listed | Re-proves existing objects or duplicates an open contribution |
| Dependency depth | At most one or two unlanded prerequisites | The proof starts below several unresolved interfaces |
| One new idea | The central lemma stated in one sentence | Combines several unrelated structures |
| Concrete probe | A concrete instance exercises the route before the general theorem | The probe becomes the deliverable instead of the general theorem |
| Reusable output | The general theorem is useful beyond the example | The result is an isolated computation |
| Acceptance oracle | Build, no-sorry and axiom policy, named test theorem fixed | "It should compile" is the only validation plan |
| Convention lock | Signature, normalization, direction, operand order explicit | The target depends on informal convention matching |
| Stop condition | A useful result exists if the generalization is abandoned | The work is all-or-nothing |
| Timebox | A short reconnaissance spike has an end | Feasibility is inferred only from the spec |

## Operational algorithm

1. Read the narrative spec and the exact library declarations the unit will consume.
2. Run a concrete probe: the smallest instance that exercises the route, and its expected normal form.
3. Test the probe without building the general abstraction.
4. Deliver the general theorem the probe supports; extract the one reusable result.
5. Land the theorem and its supporting units separately.
6. Stop or expand only after the acceptance oracle passes.

## Slice, route, and navigation

- [ ] Slice defined: the attack angle and the principles behind it (generality-first, dependency-first, reusable infrastructure first).
- [ ] Route defined: the ordered work units and the navigation factors, including steering clear of others' active work where feasible, but not always (avoid over-avoiding proximity).
- [ ] Route revisited: as work units accumulate, reusable bits (shared criteria, extractable or upstreamable API, conventions to lock) are identified and the next units updated.

## Reading the attack map

- [ ] Dependency spine identified: which targets unlock which.
- [ ] Frontier located: the boundary between done and open.
- [ ] Second-half open targets checked.
- [ ] Acceptance oracle noted per candidate target.

## Work unit vocabulary

- [ ] Work unit may naturally map to a pull request where the project uses them; the checklist applies to the unit either way.
