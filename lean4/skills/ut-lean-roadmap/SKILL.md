---
name: ut-lean-roadmap
description: "Select and revise formalization routes and slices from a roadmap: name the mathematical summit, trace the live dependency subgraph, identify branches and handoffs, and choose one coherent schedulable milestone with a stable prerequisite closure and a real downstream consumer."
---

# `ut-lean-roadmap`

## Terms

- **Roadmap:** the human-maintained account of the formalization's goals and
  mathematical dependencies. It may combine narrative, declarations, and
  examples.
- **Layer:** targets occupying a shared position in the logical dependency
  structure. Thematic numbering need not be proof order.
- **Route:** a revisable dependency subgraph toward a named mathematical
  summit. It may branch, share junctions with other routes, and reconverge.
- **Slice:** one coherent schedulable milestone selected from a route, with a
  stable prerequisite closure and a named downstream consumer.

## Procedure

Project policy may supply private route maps, goal registries, or decisions as
context. Read them in place and use them to constrain selection; do not copy
their project-specific content into the reusable skill or unrelated output.

### 1. Establish authority and live state

Read the narrative roadmap, its relevant declarations, and current human
decisions. Treat declaration stubs as targets, not proof that a milestone is
complete. Reconcile merged work, active work, and known collisions.

### 2. Trace the route

Name the summit. Trace the dependency subgraph that reaches it in topological
proof order. Record material parallel branches, shared junctions, and what is
handed off at each junction. Do not infer proof order from layer numbers or
avoid shared prerequisites merely because another route also uses them.

### 3. Compute the prerequisite closure

For each candidate milestone, classify every prerequisite as stable and
available, an explicit active dependency, or absent. An absent ordered
prerequisite blocks the slice. An active dependency makes its public contract
provisional; if that contract changes materially, reopen selection and design
for its consumers.

### 4. Select the slice

Choose a named roadmap milestone that:

- directly advances the route toward its summit;
- has a concrete downstream consumer;
- forms one reviewable mathematical boundary, including inseparable supporting
  results but excluding independent reusable work;
- uses the natural generality justified by the target, proof, and consumer;
- has an explicit, stable prerequisite closure.

Do not schedule a theorem's internal proof step as a separate milestone unless
it is independently reusable and consumed. Do not select nearby API that does
not reduce a route dependency.

### 5. Hand off to recon and design

Use `ut-lean-recon` to verify the existing-library boundary, current APIs, and
collisions. Use `ut-lean-design` to fix hypotheses, conventions, the public
contract, proof shape, and consumer tests. Run a feasibility probe only when
one of those points is genuinely uncertain.

### 6. Revisit

The roadmap and route are records of current human intent, not immutable
contracts. Recompute the route when mathematics, accepted interfaces, or goals
change. If the preferred route has no schedulable milestone, descend to its
missing prerequisites; if none qualifies, choose another uncovered roadmap
summit and repeat. Stop scheduling once the summit is landed; treat worked
examples or acceptance tails as separate goals when they matter.

## Output

Record the summit, route subgraph, selected milestone, prerequisite closure,
consumer, natural generality, and any junction handoff. Project-specific
fronts, pull-request gates, monitors, and approval rules belong in project
policy.

## Related skills

- `ut-lean-recon`: pinned API and library-boundary reconnaissance
- `ut-lean-design`: detailed declaration and proof design for the selected slice
- `ut-lean-review`: independent review after implementation
