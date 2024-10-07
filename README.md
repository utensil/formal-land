# Formal Land

My monorepo for formalization.

## Included explorations

[![Lean 4 CI](https://github.com/utensil/formal-land/actions/workflows/lean4.yml/badge.svg)](https://github.com/utensil/formal-land/actions/workflows/lean4.yml) [![Aya CI](https://github.com/utensil/formal-land/actions/workflows/aya.yml/badge.svg)](https://github.com/utensil/formal-land/actions/workflows/aya.yml) [![TLA+ CI](https://github.com/utensil/formal-land/actions/workflows/tla.yml/badge.svg)](https://github.com/utensil/formal-land/actions/workflows/tla.yml)

I explore with the following formalization systems, and do interactive [literate programming](https://en.wikipedia.org/wiki/Literate_programming) when supported, because then one can interact with the formalization and inspect intermediate (goal) states just from a Web browser.

- [Lean 4](./lean4/README.md)
  - [example index](https://utensil.github.io/formal-land/lean4/)
- [Aya](./aya/README.md)
  - [haskeller-tutorial](https://utensil.github.io/formal-land/aya/haskeller-tutorial.html)
  - [prover-tutorial](https://utensil.github.io/formal-land/aya/prover-tutorial.html)
  - [literate](https://utensil.github.io/formal-land/aya/literate.html)
- [TLA+](./tla/README.md)
  - [pluscal.pdf](https://utensil.github.io/formal-land/tla/pluscal.pdf)

## In scope

- [Coq](https://coq.inria.fr/) ([renaming](https://coq.discourse.group/t/coq-community-survey-2022-results-part-iv-and-itp-paper-announcement/2001) to Rocq): an interactive theorem prover
  - particularly with [math-from-nothing](https://github.com/sudgy/math-from-nothing)
- [Charon](https://github.com/AeneasVerif/charon): process Rust crates and convert them into files easy to handle by program verifiers
- [Kani](https://github.com/model-checking/kani): a bit-precise model checker for Rust, particularly useful for verifying unsafe code blocks
- [Aneris](https://github.com/logsem/aneris): a higher-order distributed concurrent separation logic for developing and verifying distributed systems, built on Iris and Coq
- [Dafny](https://dafny.org/): a verification-aware programming language that has native support for recording specifications and is equipped with a static program verifier, used by [Cedar](https://github.com/cedar-policy) before [porting to Lean 4](https://github.com/cedar-policy/rfcs/blob/main/text/0032-port-formalization-to-lean.md)
