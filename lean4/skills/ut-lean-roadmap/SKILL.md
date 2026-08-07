---
name: ut-lean-roadmap
description: "Read, evaluate, and select routes on a layered Lean formalization roadmap: the six-checkpoint pipeline, the by-dimension checks, route evaluation, the attack map, and roadmaps as records of human intent."
---

# ut-lean-roadmap: working with a Lean formalization roadmap

## Purpose

A formalization roadmap organizes Lean work into layers with dependency spines: which targets exist, in what order they unlock each other, and which are still open. This skill covers how to read such a roadmap, how to evaluate a candidate slice against it, and how to choose a route through it.

## When to use

- Choosing the next contribution to a layered formalization roadmap.
- Evaluating whether a proposed slice is the right size and shape for one pull request.
- Reading a roadmap's structure to find where the frontier is.
- Writing or improving a roadmap so it carries usable intent signals.

## Procedure

### 1. The six-checkpoint pipeline

A candidate slice becomes a pull request through six checkpoints:

1. Roadmap fit: the slice attacks an exact target, a named declaration or theorem family in the roadmap.
2. Slice shape: one pull request, one idea. The slice has dependency value, a natural generic statement, and a direct downstream consumer, recorded in the research record before any edit.
3. Reuse and feasibility: the existing library objects to reuse are listed, the missing theorem is named, and the proof route is sketched.
4. Boundary gate: the slice stays in its lane. Crossing into another work area (application-specific representations, numerical work, generic library extraction) requires an explicit scope decision.
5. Collision scan: recheck the roadmap, the open pull requests and their claims, and other people's claims before starting.
6. Human gate: opening a pull request is a human checkpoint, not a default.

### 2. The checks by dimension

Math, what the theorem is:

- One new idea: the central lemma can be stated in one sentence; the target is not a bundle of several unrelated structures.
- Small instance first: one low-dimensional or finite example exercises the route before the general theorem.
- Reusable output: the general theorem is useful beyond the example.
- Convention lock: signature, normalization, basis order, action, and operand order are explicit up front.
- Stop condition and timebox: a useful result exists if the generalization is abandoned, and a reconnaissance spike has a concrete end.

Lean, how it must be built:

- Existing-library boundary: reuse the library's objects; do not re-prove what exists or duplicate an open pull request.
- Dependency depth: at most one or two unlanded prerequisites.
- Acceptance oracle: build, no-sorry and axiom policy, and a named test theorem are fixed, not just "it should compile".
- Consumer probe: a non-unfolding consumer or a bare-simp probe confirms the public API is usable before the first edit.
- Natural generality: if the proof is uniform in a degree, state it for all degrees.

Roadmap, why it belongs:

- Exact target: a named declaration or theorem family.
- Definitive spec: the README is definitive; a sorry-target stub is explicitly non-exhaustive.
- Dependency value: a known unmet prerequisite beats nearby but non-enabling API; no scope stretch to chase a dependency.
- Downstream consumer: the direct consumer of the slice is named.

Process, the record:

- P0 record, before any edit: dependency value, one-pull-request boundary, collision result, natural generic statement, direct downstream consumer.
- P1 record, before the first Lean edit: exact public API, reused structural API, consumer probe, intended proof route. The first Lean edit happens after P1.

### 3. Evaluating a route

- The README is definitive: a stub file with sorry targets supplies signatures but cannot alone establish that a layer or prerequisite is complete. Matching a stub signature does not complete a milestone.
- Dependency-value selection: pick the known unmet prerequisite over nearby but non-enabling API. Never stretch scope to chase a dependency.
- One-pull-request boundary: one topic per pull request. Ship a prerequisite refactor as its own pull request.
- Convention locks: an irreconcilable convention difference keeps a result in the project rather than upstream, unless the convention is fixed by an explicit decision.
- The ten-gate slice rubric: exact target; existing-library boundary; dependency depth; one new idea; small instance; reusable output; acceptance oracle; convention lock; stop condition; timebox. Each gate has an explicit fail condition (see ROUTES.md).
- Operational algorithm: search the repository and open pull requests; read the exact library declarations; write the smallest concrete instance and its expected normal form; test it without building the general abstraction; extract the one reusable theorem; land theorem and instance as separate milestones; stop or expand only after the acceptance oracle passes.

### 4. Reading the attack map

A roadmap is layers with dependency spines. To see the frontier:

- Read the dependency spine: which layer each layer needs, and which layers are reachable directly from the core. A structure theorem proved forward from the module, a double cover that is the single hardest target, and layers that open the second half of the roadmap all shape the order of work.
- The second half of the roadmap is where the open targets live. First-half layers get crowded with foundation work; once the spine is in place, later layers are untouched and open.
- Classify each layer as heavily worked, substrate done, in progress, or untouched. The frontier is the boundary between done and open.
- Acceptances pin each layer: a concrete named result (a dimension formula, an isomorphism, a specific counterexample) that the layer must reach.

### 5. Roadmaps as records of human intent

A roadmap is a record of human intent, not a corpus of generated prose. It is useful to the extent that it carries clear intent signals and receives quality feedback:

- Commit history and edit rationale carry more intent than polished paragraphs.
- Short, pointed targets with explicit acceptance oracles beat long descriptive passages.
- A roadmap without quality feedback (review, correction, contested claims) is noise.
- When improving a roadmap, aim for signals a newcomer can act on: exact targets, named dependencies, acceptance oracles, and a visible frontier.

## References

- ROUTES.md in this directory: the pipeline and gates as a checklist.
