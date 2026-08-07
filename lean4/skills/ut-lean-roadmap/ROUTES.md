# ROUTES.md: slice evaluation checklist

This file turns the skill's pipeline and gates into a checklist to run before opening a pull request.

## The six checkpoints

1. [ ] Roadmap fit: exact target named in the roadmap.
2. [ ] Slice shape: one pull request, one idea.
3. [ ] Reuse and feasibility: library route sketched.
4. [ ] Boundary gate: lane checked; no unapproved crossing.
5. [ ] Collision scan: no duplicate of an open pull request or claim.
6. [ ] Human gate: the opening is a human checkpoint.

## Checks by dimension

Math:

- [ ] One new idea: the central lemma fits in one sentence.
- [ ] Small instance: a low-dimensional or finite case exercises the route.
- [ ] Reusable output: the general theorem is useful beyond the example.
- [ ] Convention lock: signature, normalization, basis order, action, operand order explicit.
- [ ] Stop condition: a useful result exists if the generalization is abandoned.
- [ ] Timebox: the reconnaissance spike has a concrete end.

Lean:

- [ ] Existing-library boundary: objects to reuse listed, missing theorem named.
- [ ] Dependency depth: at most one or two unlanded prerequisites.
- [ ] Acceptance oracle: build, no-sorry and axiom policy, named test theorem.
- [ ] Consumer probe: a non-unfolding consumer or bare-simp probe passes.
- [ ] Natural generality: uniform-degree proofs stated for all degrees.

Roadmap:

- [ ] Exact target: named declaration or theorem family.
- [ ] Definitive spec: README is definitive; a sorry-target stub is non-exhaustive.
- [ ] Dependency value: an unmet prerequisite beats non-enabling API.
- [ ] Downstream consumer named.

Process:

- [ ] P0 record: dependency value, one-pull-request boundary, collision result, natural generic statement, downstream consumer.
- [ ] P1 record: exact public API, reused structural API, consumer probe, proof route.
- [ ] The first Lean edit is after P1.

## The ten-gate slice rubric

| Gate | Required evidence | Fail condition |
| --- | --- | --- |
| Exact target | Named declaration or theorem family in the roadmap | The goal is only a topic |
| Existing-library boundary | Library objects to reuse and the missing theorem listed | Re-proves existing objects or duplicates an open pull request |
| Dependency depth | At most one or two unlanded prerequisites | The proof starts below several unresolved interfaces |
| One new idea | The central lemma stated in one sentence | Combines several unrelated structures |
| Small instance | One low-dimensional or finite example exercises the route | Only the fully general theorem is specified |
| Reusable output | The general theorem is useful beyond the example | The result is an isolated computation |
| Acceptance oracle | Build, no-sorry and axiom policy, named test theorem fixed | "It should compile" is the only validation plan |
| Convention lock | Signature, normalization, basis order, action, operand order explicit | The target depends on informal convention matching |
| Stop condition | A useful result exists if the generalization is abandoned | The project is all-or-nothing |
| Timebox | A short reconnaissance spike has a concrete end | Feasibility is inferred only from the README |

## Operational algorithm

1. Search the repository and open pull requests.
2. Read the exact library declarations.
3. Write the smallest concrete instance and its expected normal form.
4. Test it without building the general abstraction.
5. Extract the one reusable theorem.
6. Land theorem and instance as separate milestones.
7. Stop or expand only after the acceptance oracle passes.

## Reading the attack map

- [ ] Dependency spine identified: which layers unlock which.
- [ ] Frontier located: the boundary between done and open.
- [ ] Second-half layers checked for open targets.
- [ ] Each candidate layer's acceptance oracle noted.
