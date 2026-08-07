---
name: ut-lean-roadmap
description: "Work with a formalization roadmap: layers as logical dependency structure, slices as chosen attack angles, routes as practical evolving plans, and work units as concrete deliverables. Generality-first: each unit delivers the general theorem, with concrete probes only as feasibility spikes."
---

# ut-lean-roadmap: working with a formalization roadmap

## Definitions

The key terms are used throughout; define them up front.

- **Roadmap**: the organizing document of a formalization effort. Its form varies (a narrative README, a blueprint, a set of notes, a stub file with sorry targets).
- **Layer**: a logical dependency structure in a roadmap: a group of targets that share a position in the dependency order and unlock the layers above them.
- **Slice**: the picked attack angle on the roadmap, chosen from your principles and preferences (generality-first, dependency-first, a preference for reusable infrastructure, and so on). A slice may overlap with others' work.
- **Route**: the practical plan to work on a slice: the ordered sequence of work units, chosen by navigating more factors than the slice alone, including steering clear of others' active work where feasible (but not always: avoid over-avoiding proximity). A route is a plan, not a contract; it evolves as work units accumulate.
- **Work unit**: the concrete deliverable of one step in a route: a theorem, construction, or refactor with a clear dependency and a clear consumer. A work unit may naturally map to a pull request where the project uses them.

## Purpose

A formalization roadmap organizes work into layers with dependency spines: which targets exist, in what order they unlock each other, and which are still open. This skill covers how to read such a roadmap in whatever form a project uses, how to pick a slice, how to plan a route, and how to select the next work unit. It is methodology, not policy: the vocabulary is the work unit, not any project's contribution process, and the checks apply to any roadmap shape.

## When to use

- Choosing the next work unit on a layered formalization roadmap.
- Evaluating whether a proposed unit is the right size, shape, and scope.
- Reading a roadmap to find where the frontier is.
- Writing or improving a roadmap so it carries usable intent signals.

## Core principle: generality first

The deliverable is always the general theorem or construction the roadmap names. Concrete cases are probes: a spike on a concrete instance can establish feasibility and pin a convention, but the work unit stays the general result. Never let the probe become the deliverable, and never state a theorem at a fixed case when the argument is uniform: if the proof works for every degree, index, or structural parameter, state it so.

## Reading a roadmap

Read the form first:

- The narrative spec anchors the work. Whatever its form, it is read before the definitions and signatures; a signature-stub file supplies targets but cannot alone establish that a milestone is complete. Matching a stub signature is not completing the milestone.
- Find the layers and their dependency spine: which layer each layer needs, which targets unlock others, and which are reachable directly from the core.
- Locate the frontier: classify each area as heavily worked, substrate done, in progress, or untouched. The frontier is the boundary between done and open, and the second half of a roadmap is where the open targets live.
- Collect the acceptance oracles: concrete named results (a formula, an isomorphism, a counterexample, any check the subject admits) that each layer must reach. Use the vocabulary the subject supports; do not presuppose dimension, finiteness, or any structure the mathematics may not have.

## Selecting the next work unit

Each work unit is selected as the next unit in a route: scoped, of manageable scale and complexity, with clear dependencies and a clear consumer. (A work unit may naturally map to a pull request.)

- Named target: the unit attacks a named declaration, theorem family, or milestone in the roadmap, not a topic.
- One idea: the central lemma can be stated in one sentence; a prerequisite refactor is its own unit.
- Dependencies: at most one or two unlanded prerequisites; list the library objects the unit will reuse and the missing theorem it supplies.
- Consumer: the direct downstream consumer of the unit is named.
- Dependency value: prefer a known unmet prerequisite over nearby but non-enabling work; do not stretch scope to chase a dependency.
- Natural generality: state the unit at the level the roadmap names; uniform arguments are stated for all degrees or structures.
- Collisions: recheck the roadmap and the open contributions and claims before starting.
- Boundary: crossing into another work area (application-specific representations, numerical work, generic library extraction) is an explicit decision, not a default.
- Convention lock: signature, normalization, direction, and operand order are explicit before the proof, and pinned by small definitional tests where the subject admits them.
- Feasibility probe: a concrete spike (the smallest instance that exercises the route) can establish the route and the expected normal form; test it without building the general abstraction, then deliver the general theorem it supports.
- Acceptance oracle and stop condition: build, no-sorry and axiom policy, and a named test theorem are fixed; a useful result exists if the generalization is abandoned; a spike has an end.

## Slices, routes, and navigation

A slice is your attack angle; a route is how you actually work it. Keep them separate:

- The slice states the principles behind the angle (generality-first, dependency-first, reusable infrastructure first). It may overlap with what others are doing; the roadmap does not have to be carved into disjoint slices.
- The route navigates in practice: it orders the work units, and it steers around more factors than the slice alone. When others are actively working nearby, steer clear slightly where feasible, but not always: proximity is sometimes exactly right (building on their work, converging on a shared abstraction), and over-avoiding is its own cost.
- A route is revisited from time to time. As work units accumulate, the reusable bits gradually surface: the criterion shared by several units, the structural API worth extracting or upstreaming, the conventions that should have been locked earlier. Each revisit updates the next units. The slice may stay the same; the route evolves.

## Roadmaps as records of human intent

A roadmap is a record of human intent, not a corpus of generated prose. It is useful to the extent that it carries clear intent signals and receives quality feedback: commit history and edit rationale carry more intent than polished paragraphs; short pointed targets with explicit acceptance oracles beat long descriptive passages; a roadmap without review, correction, or contested claims is noise. When improving a roadmap, aim for signals a newcomer can act on: exact targets, named dependencies, acceptance oracles, and a visible frontier.

## References

- ROUTES.md in this directory: the runnable checklist and the gate table.
- Related skills in this set: ut-lean-design for designing individual units, ut-lean-recon for the API reconnaissance that supports unit selection, ut-lean-review for reviewing the units a roadmap produces.
