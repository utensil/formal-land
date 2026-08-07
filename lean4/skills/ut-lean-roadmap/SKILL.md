---
name: ut-lean-roadmap
description: "Work with a formalization roadmap: layers as logical dependency structure, routes picked through the roadmap (the attack angle and the practical plan, evolving as slices accumulate), and slices as the selected next unit of work, naturally mapping to a pull request. Generality-first: each slice delivers the general theorem, with concrete probes only as feasibility spikes."
---

# ut-lean-roadmap: working with a formalization roadmap

## Definitions

The key terms are used throughout; define them up front.

- **Roadmap**: the organizing document of a formalization effort. It consists of layers, and you pick a route through it. Its form varies (a narrative README, a blueprint, a set of notes, a stub file with sorry targets).
- **Layer**: a logical dependency structure in a roadmap: a group of targets that share a position in the dependency order and unlock the layers above them.
- **Route**: the route picked through the roadmap: the attack angle (chosen from your principles and preferences: generality-first, dependency-first, a preference for reusable infrastructure) together with the practical plan that works it. A route navigates by more factors than the angle alone, including steering clear of others' active work where feasible (but not always: avoid over-avoiding proximity). A route is a plan, not a contract; it evolves as slices accumulate.
- **Slice**: the next slice of work, selected from the route and designed: scoped, of manageable scale and complexity, with clear dependencies and a clear consumer. A slice naturally maps to a pull request where the project uses them.

## Purpose

A formalization roadmap organizes work into layers with dependency spines: which targets exist, in what order they unlock each other, and which are still open. You pick a route through the roadmap and select the next slice of work along it. This skill covers how to read such a roadmap in whatever form a project uses, how to pick and navigate a route, and how to select and scope the next slice. It is methodology, not policy: the vocabulary is the slice, not any project's contribution process, and the checks apply to any roadmap shape.

## When to use

- Selecting the next slice of work on a layered formalization roadmap.
- Evaluating whether a proposed slice is the right size, shape, and scope.
- Reading a roadmap to find where the frontier is.
- Writing or improving a roadmap so it carries usable intent signals.

## Core principle: generality first

The deliverable is always the general theorem or construction the roadmap names. Concrete cases are probes: a spike on a concrete instance can establish feasibility and pin a convention, but the slice delivers the general result. Never let the probe become the deliverable, and never state a theorem at a fixed case when the argument is uniform: if the proof works for every degree, index, or structural parameter, state it so.

## Reading a roadmap

Read the form first:

- The narrative spec anchors the work. Whatever its form, it is read before the definitions and signatures; a signature-stub file supplies targets but cannot alone establish that a milestone is complete. Matching a stub signature is not completing the milestone.
- Find the layers and their dependency spine: which layer each layer needs, which targets unlock others, and which are reachable directly from the core.
- Locate the frontier: classify each area as heavily worked, substrate done, in progress, or untouched. The frontier is the boundary between done and open, and the second half of a roadmap is where the open targets live.
- Collect the acceptance oracles: concrete named results (a formula, an isomorphism, a counterexample, any check the subject admits) that each layer must reach. Use the vocabulary the subject supports; do not presuppose dimension, finiteness, or any structure the mathematics may not have.

## Selecting the next slice

Each slice is selected as the next unit in a route: scoped, of manageable scale and complexity, with clear dependencies and a clear consumer. A slice naturally maps to a pull request.

- Named target: the slice attacks a named declaration, theorem family, or milestone in the roadmap, not a topic.
- One idea: the central lemma can be stated in one sentence; a prerequisite refactor is its own slice.
- Dependencies: at most one or two unlanded prerequisites; list the library objects the slice will reuse and the missing theorem it supplies.
- Consumer: the direct downstream consumer of the slice is named.
- Dependency value: prefer a known unmet prerequisite over nearby but non-enabling work; do not stretch scope to chase a dependency.
- Natural generality: state the slice at the level the roadmap names; uniform arguments are stated for all degrees or structures.
- Collisions: recheck the roadmap and the open contributions and claims before starting.
- Boundary: crossing into another work area (application-specific representations, numerical work, generic library extraction) is an explicit decision, not a default.
- Convention lock: signature, normalization, direction, and operand order are explicit before the proof, and pinned by small definitional tests where the subject admits them.
- Feasibility probe: a concrete spike (the smallest instance that exercises the route) can establish the route and the expected normal form; test it without building the general abstraction, then deliver the general theorem it supports.
- Acceptance oracle and stop condition: build, no-sorry and axiom policy, and a named test theorem are fixed; a useful result exists if the generalization is abandoned; a spike has an end.

## Routes, picked and navigated

The route is picked through the roadmap; the slice is selected from it. Keep the two apart:

- The route carries the attack angle: the principles behind your approach (generality-first, dependency-first, reusable infrastructure first). It may overlap with what others are doing; the roadmap does not have to be carved into disjoint angles.
- The route navigates in practice: it orders the slices, and it steers around more factors than the angle alone. When others are actively working nearby, steer clear slightly where feasible, but not always: proximity is sometimes exactly right (building on their work, converging on a shared abstraction), and over-avoiding is its own cost.
- A route is revisited from time to time. As slices accumulate, the reusable bits gradually surface: the criterion shared by several slices, the structural API worth extracting or upstreaming, the conventions that should have been locked earlier. Each revisit updates the next slices. The route evolves; the roadmap stays.

## Roadmaps as records of human intent

A roadmap is a record of human intent, not a corpus of generated prose. It is useful to the extent that it carries clear intent signals and receives quality feedback: commit history and edit rationale carry more intent than polished paragraphs; short pointed targets with explicit acceptance oracles beat long descriptive passages; a roadmap without review, correction, or contested claims is noise. When improving a roadmap, aim for signals a newcomer can act on: exact targets, named dependencies, acceptance oracles, and a visible frontier.

## References

- ROUTES.md in this directory: the runnable checklist and the gate table.
- Related skills in this set: ut-lean-design for designing a selected slice, ut-lean-recon for the API reconnaissance that supports slice selection, ut-lean-review for reviewing the slices a roadmap produces.
