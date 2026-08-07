# VERIFY.md: the verification discipline for executable Lean content

This file expands section 5 of SKILL.md and applies only to projects that
carry executable content: computed programs, native oracles, or float
kernels. Pure formalization projects, whose deliverables are declarations and
proofs, never need this file; it exists because a few Lean projects embed a
program inside the formalization and must state exactly what is proved about
it.

## One authority, several proved representations

The verification chain for a project with executable content keeps these layers distinct and proves the bridges between them:

1. Reference specification: the exact operation, stated over the abstract object (for example, an algebra in the library).
2. Denoted abstract object: the mathematical structure the specification talks about.
3. Executable implementation: the concrete program (arrays, bit masks, loops) that computes the operation.
4. Shape, bounds, and termination: the executable code is total, with a fixed output shape, every read and write in bounds, and the reduction order explicit.
5. Functional correctness: for every well-formed input, decoding the executable output equals the semantic result. This is a universal theorem, not a set of example tests.
6. Kernel equivalence: every optimized, specialized, or otherwise distinct kernel is proved equivalent to the reference implementation, so there is one semantic product and several proved refinements.
7. Trusted boundaries: state explicitly what is trusted rather than proved: the compiler and code generation, foreign function interface calls, external JITs, SIMD or GPU kernels, and floating-point arithmetic.

Definitions that merely resemble each other do not establish refinement. Two separately implemented multiplication functions with no theorem tying the executed kernel to the semantic product are not a verification chain. Example tests without a universal theorem are not correctness.

## Truthfulness about floating point

- Never install a false algebraic instance on a floating-point type. IEEE floats are not a commutative ring, so a ring instance on a float type is a lie. If a raw operations layer is needed, define one that carries no laws at all, with the exact evaluation order fixed.
- A structural float smoke test (the storage shape and loop structure running with float coefficients) is exactly that: a smoke test. It is not a numerical-correctness claim. State its status honestly.
- A numerical-correctness claim requires a separately accepted contract: exceptional-value behavior (NaN, infinities, signed zero, subnormals where supported, and an explicit policy where they are absent), the rounding model for each primitive, and an accumulated absolute and relative error bound for the fixed reduction order.
- NaN comparisons must return false. A predicate that silently passes NaN is a lie.
- "It runs numerically" is never reported as "it is numerically verified."

## Benchmark honesty

Performance results are evidence only under a preregistered protocol:

- Separate the measurement classes: single-operation latency, batch throughput, and representative workloads. They answer different questions and must not be pooled.
- Pin compiler version and flags, enabled library features, target ISA and hardware, data layout, input distribution, and build mode.
- Before comparing two implementations, establish an equivalence check that they perform equal work. Comparing different amounts of work is not a benchmark.
- Propose the protocol and the numeric budgets before measuring. A threshold revised after observing the measurement is not evidence.

## Acceptance oracle

Every verification step ends with a named acceptance oracle: a universal theorem, not examples. "It compiles" and "a few test cases pass" are not acceptance. The oracle is a specific named statement (for example, decode-after-multiply for all well-shaped inputs) that the build must prove, together with the no-sorry and axiom audit from SKILL.md.

## Rejection list

Reject a verification claim if any of these appears:

- a hard-coded result table used as the implementation or the proof;
- a noncomputable placeholder, axiom, sorry, or admit on the executable path;
- semantic and executable implementations with no theorem tying the executed kernel to the semantic operation;
- example tests without a universal theorem;
- exact evaluation performed outside the same kernel named in the theorem;
- a small degenerate case presented as the representative application;
- performance thresholds chosen or revised after observing measurements;
- a claim that floating-point computation refines the exact arithmetic without a separately selected and proved correctness contract;
- a report that omits exact source revisions, commands, exit codes, or an honest classification of what is proved versus what is trusted.
