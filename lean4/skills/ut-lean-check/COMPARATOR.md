# COMPARATOR.md: the comparator harness in detail

## What it answers

The comparator answers three questions about a solution:

1. Does the solution prove exactly the stated theorem, over unweakened definitions?
2. Does the proof use only the permitted axioms?
3. Does an independent implementation of the Lean kernel accept the proof term?

## Why the challenge file is short

A challenge file is short because it contains only the definitions needed to state the theorem plus the theorem declarations with `sorry` bodies. All proofs live in the solution. The `lean4export` tool dumps kernel-level declarations from the compiled `.olean` of each module (separate builds), and the comparator compares the transitive closure of the listed theorem names. The solution cannot prove "the same theorem" with a weakened definition, because every referenced constant must be bit-for-bit identical in the two exports.

## Config anatomy

- `challenge_module`, `solution_module`: the compiled module names.
- `theorem_names`: every theorem to check; list every entry when the statement splits into several theorems.
- `definition_names`: optional; for each name, the comparator additionally ensures the solution's definitional unfolding stays within the challenge's definition, so the solution cannot hide a changed definition behind a private name.
- `permitted_axioms`: the exact axiom closure allowed for the proof terms.
- `enable_nanoda`: re-type-check the exported proof term with the nanoda kernel. The `nanoda_bin` binary must be on PATH or named by the comparator's environment variable.

## The independent kernel

nanoda is a Rust implementation of the Lean kernel, distributed as a library and a `nanoda_bin` binary. With `enable_nanoda: true`, the exported proof term is piped to nanoda and re-type-checked. The trust assumption becomes "the Lean or the nanoda kernel is correct": the two kernels are independent implementations, so a bug in one is caught by the other.

Community context: the Lean community reviews comparator challenge files in public, so a challenge file is a public artifact with a real audience. Recent soundness-bug reports against the Lean kernel motivated the independent-kernel layer: a theorem is stronger evidence when a second, independently written kernel accepts the same proof term.

## Trust assumptions, stated by the comparator

Running the comparator and believing its result assumes:

- the build and comparison run in a sandbox that cannot be escaped (a Landlock-based sandbox);
- the Lean kernel is correct, reduced by nanoda to "the Lean or the nanoda kernel is correct";
- the run is not privileged (sandbox escapes under a privileged user are easier).

State these assumptions in any report of the result.

## Operational checklist

- [ ] Challenge module imports only the library (for example `import Mathlib`); no imports from the solution.
- [ ] Challenge states the theorem verbatim, with `sorry` bodies, and all vocabulary needed to read it.
- [ ] The statement set is pinned: the challenge is the auditable record of exactly what was proved.
- [ ] Config lists every theorem name (and definition names where relevant).
- [ ] Permitted axioms are explicit and minimal.
- [ ] `enable_nanoda: true` and `nanoda_bin` available.
- [ ] Solution build is sandboxed; the sandbox cannot be escaped from an adversarial module.
- [ ] Axiom audit via `#print axioms` stays green.
- [ ] A person who has not seen the solution can read the challenge and know what is being claimed.
