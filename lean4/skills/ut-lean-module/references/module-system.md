# Lean module-system guide

## Imports and visibility

An ordinary `import` makes a module's exported environment available. Use
`public import` when downstream users should receive that dependency through
the current module, and `private import` for implementation-only dependencies
when supported by the project's Lean version.

```lean
import Mathlib.Algebra.Group.Basic
private import Project.Internal.FastLemma
public import Project.Definitions.Curve
```

Probe a three-module example before changing a large cone. A private import is
still available while compiling its importer, but should not enlarge every
consumer's environment.

## Sections and declaration visibility

`public section` and `private section` control declarations made inside them.
Private declarations receive generated names and are not stable API. Keep proof
helpers private only after checking that no downstream statement or definition
names them.

Preserve `variable`, `include`, `open`, notation, options, and universe context
when moving declarations. A generated statement module and its proof module
must agree on the exact public namespace and binders.

## Safe proof extraction

Do not locate a proof by searching for the first `:=`: types can contain `let`,
nested terms, `where` blocks, macros, or wrappers. Use Lean declaration spans
and value/proof positions. Keep the exact header and type in a statement stub;
keep the proof-side context and imports in the proof module. Compile generated
files immediately.

Compiler-generated equation lemmas and match auxiliaries have no source span;
regenerate them with their parent declaration instead of splitting them.

## Dependencies and attributes

Instances are dependency roots even when they do not occur in a proof term.
`attribute [-instance]` changes typeclass search and `attribute [-simp]` changes
the simplifier in the current environment. Treat generated lists as controls:
compare names with the reachable environment, remove a small batch, then build
the exact module and all reverse consumers.

## Package roots

Lake packages and `lean_lib` roots affect the exported graph. A shaker run over
one root may be incomplete when several roots contribute to the final target.
Use the same explicit root set for analysis, shaking, and validation.
