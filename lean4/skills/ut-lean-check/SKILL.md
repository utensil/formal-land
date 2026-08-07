---
name: ut-lean-check
description: "Verify Lean proofs beyond the Lean kernel: the comparator harness with lean4export, bit-for-bit constant comparison, axiom closure, and the nanoda independent kernel, plus native-execution oracles for executable content."
---

# ut-lean-check: verifying Lean beyond the kernel

## Purpose

The Lean kernel checks proofs, but "the Lean kernel is correct" is a real assumption. This skill covers two complementary techniques for independent verification: the comparator harness, which re-checks a solution's exported kernel declarations with an independent implementation of the kernel, and the native-execution oracle, which runs an executable computation natively as complementary evidence.

## When to use

- A headline theorem with a long solution must be independently verifiable without reading the whole solution.
- The trust assumption should be weaker than "the Lean kernel is correct".
- An adversarial or untrusted solution could tamper with definitions, weakening them until the theorem becomes trivial.
- Executable content (`native_decide` or computable definitions) should be run natively as evidence, or a native check is failing and the cause must be diagnosed.

## Procedure

### Part A: the comparator harness

The comparator (github.com/leanprover/comparator) checks that a solution module proves exactly the theorem stated in a challenge module, using only permitted axioms, and re-checks the proof term in an independent kernel. Two modules participate:

- The challenge module: a short, self-contained restatement of the theorem, importing only the library (for example Mathlib). It contains the vocabulary needed to state the theorem and the theorem declarations with `sorry` bodies, and no proof content. A human or another tool can check it without ever reading the solution.
- The solution module: the real proof, which must use the same definitions so that the theorem statements are genuinely the same.

A JSON config names the modules and the check options:

```json
{
  "challenge_module": "ComparatorChallenges.MyTheorem",
  "solution_module": "MySolution",
  "theorem_names": ["MySolution.theoremA"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": true
}
```

The check pipeline:

1. `lean4export` dumps kernel-level declarations from the compiled `.olean` files of the challenge module and the solution module (separate builds). It must match the Lean version of the project.
2. The comparator walks the transitive closure of the listed theorem names and requires every referenced constant to be bit-for-bit identical between the two exports. Any tampered definition in the solution fails here.
3. The axiom closure of the solution's proof terms must be a subset of the permitted axioms.
4. With nanoda enabled, the exported proof term is re-type-checked by nanoda, an independent Rust implementation of the Lean kernel. The trust assumption drops from "the Lean kernel is correct" to "the Lean or the nanoda kernel is correct".
5. The solution build runs inside a sandbox, so an adversarial solution cannot tamper with the challenge build or the comparison.

Design rules from community practice:

- The challenge file is the crucial artifact. Keep it short and self-contained, and keep it independent of the solution. If the challenge imports the solution, tampering is invisible by construction.
- A theorem input that must not be axiomatized (for example, an abstract parameter the theorem quantifies over) stays a parameter, never an axiom.
- The permitted-axiom list is the audit contract. Kernel soundness bugs have been reported against Lean itself, which is exactly the motivation for the independent kernel.
- The sandboxed run is Linux-only in practice; axiom auditing with `#print axioms` works anywhere.

### Part B: the native-execution oracle

When a proved executable theorem computes a concrete result, running it natively is complementary evidence. The diagnosis chain treats three obstructions as distinct:

1. `rfl` failure: the equality is not definitional. The computation does not unfold to the expected form. This is a reducibility question.
2. Kernel `decide` stoppage: kernel reduction stops somewhere in the computation, for example at a large structure it will not unfold.
3. Native-linkage failure: native compilation cannot reach an imported executable body, because module facets can hide definitions from native compilation.

Fixes, in order:

- `public meta import` in the oracle module makes imported executable bodies available to native compilation. Keep it local to the oracle module, not global.
- Scope every `nativeDecide` linter exception to its theorem. A blanket exception hides future violations.
- Keep the representation and the proved theorem unchanged. The oracle runs the same kernel calls the refinement theorem names; it is not a new implementation.

Label the result honestly: a trusted executable oracle, complementary evidence, never a replacement for the refinement theorem. Numeric predicates must return false for NaN comparisons.

## References

- Comparator: https://github.com/leanprover/comparator
- nanoda, the independent kernel: https://github.com/ammkrn/nanoda_lib
- Lean manual on `native_decide`: https://lean-lang.org/lean4/doc/native_decide.html
- COMPARATOR.md in this directory: the harness anatomy and community context in detail.
- Related skills: ut-lean-ops (toolchain-level verification), ut-lean-recon (the evidence the checker verifies).
