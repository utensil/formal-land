# ROUTES.md: slice checklist

Run this before committing to a roadmap slice. It is the executable form of the skill's methodology; it does not restate the prose in SKILL.md.

## Slice selection

- [ ] Named target in the roadmap, not a topic.
- [ ] One idea: the central lemma fits in one sentence; a prerequisite refactor is its own slice.
- [ ] General theorem is the deliverable; any concrete spike is only a probe.
- [ ] Natural generality: uniform arguments stated for all degrees or structures.
- [ ] Clear dependencies: at most one or two unlanded prerequisites; library objects to reuse listed.
- [ ] Live prerequisite closure recorded: every prerequisite is merged, an explicit active dependency, or absent; no absent ordered prerequisite is crossed.
- [ ] Named downstream consumer.
- [ ] Dependency value: an unmet prerequisite beats non-enabling nearby work; no scope stretch.
- [ ] Collision scan: no duplicate of an open contribution or claim.
- [ ] Boundary: no unapproved crossing into another work area.
- [ ] Convention lock: signature, normalization, direction, operand order explicit, pinned by definitional tests where the subject admits them.
- [ ] Acceptance oracle: build, no-sorry and axiom policy, named test theorem fixed.
- [ ] Stop condition and timebox: a useful result exists if the generalization is abandoned; the spike has an end.
- [ ] A material prerequisite-contract change reopens selection and design for every provisional dependent slice.

## The gate table

| Gate | Required evidence | Fail condition |
| --- | --- | --- |
| Exact target | Named declaration, theorem family, or milestone in the roadmap | The goal is only a topic |
| Existing-library boundary | Library objects to reuse and the missing theorem listed | Re-proves existing objects or duplicates an open contribution |
| Dependency depth | At most one or two explicit unlanded prerequisites and no absent ordered prerequisite | The proof starts below several unresolved interfaces or crosses an absent prerequisite |
| One new idea | The central lemma stated in one sentence | Combines several unrelated structures |
| Concrete probe | A concrete instance exercises the route before the general theorem | The probe becomes the deliverable instead of the general theorem |
| Reusable output | The general theorem is useful beyond the example | The result is an isolated computation |
| Acceptance oracle | Build, no-sorry and axiom policy, named test theorem fixed | "It should compile" is the only validation plan |
| Convention lock | Signature, normalization, direction, operand order explicit | The target depends on informal convention matching |
| Stop condition | A useful result exists if the generalization is abandoned | The work is all-or-nothing |
| Timebox | A short reconnaissance spike has an end | Feasibility is inferred only from the spec |

## Operational algorithm

1. Read the narrative spec and the exact library declarations the slice will consume.
2. Run a concrete probe: the smallest instance that exercises the route, and its expected normal form.
3. Test the probe without building the general abstraction.
4. Deliver the general theorem the probe supports; extract the one reusable result.
5. Land the theorem and its supporting slices separately.
6. Stop or expand only after the acceptance oracle passes.

## Routes and navigation

- [ ] Route picked through the roadmap: the attack angle (the principles behind the approach) and the practical plan.
- [ ] Route navigates in practice: ordering of slices and the navigation factors, including steering clear of others' active work where feasible, but not always (avoid over-avoiding proximity).
- [ ] Route revisited: as slices accumulate, reusable bits (shared criteria, extractable or upstreamable API, conventions to lock) are identified and the next slices updated.

## Reading the attack map

- [ ] Dependency spine identified: which targets unlock which.
- [ ] Frontier located: the boundary between done and open.
- [ ] Second-half open targets checked.
- [ ] Acceptance oracle noted per candidate target.

## Slice vocabulary

- [ ] A slice naturally maps to a pull request where the project uses them; the checklist applies to the slice either way.
