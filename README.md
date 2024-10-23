# Formal Land

My monorepo for formalization.

## Included explorations

[![Lean 4 CI](https://github.com/utensil/formal-land/actions/workflows/lean4.yml/badge.svg)](https://github.com/utensil/formal-land/actions/workflows/lean4.yml) [![Aya CI](https://github.com/utensil/formal-land/actions/workflows/aya.yml/badge.svg)](https://github.com/utensil/formal-land/actions/workflows/aya.yml) [![TLA+ CI](https://github.com/utensil/formal-land/actions/workflows/tla.yml/badge.svg)](https://github.com/utensil/formal-land/actions/workflows/tla.yml)

I explore with the following formalization systems, and do interactive [literate programming](https://en.wikipedia.org/wiki/Literate_programming) when supported, because then one can interact with the formalization and inspect intermediate (goal) states just from a Web browser.

- [Lean 4 explorations on](./lean4/README.md)
    - annotated by [alectryon](https://github.com/cpitclaudel/alectryon)
    - [Edge Lean 4](https://utensil.github.io/formal-land/lean4/)
        - preferably follow the latest Lean 4 release candidate
    - [Duper](https://utensil.github.io/formal-land/lean4-duper-xp/)
        - likely to follow a latest Lean 4 stable release
    - [Verso](https://utensil.github.io/formal-land/lean4-verso-xp/)
        - likely to follow an older Lean 4 stable release
    - [SciLean](https://utensil.github.io/formal-land/lean4-sci-xp/)
        - likely to follow an older Lean 4 unstable release
- [Aya](./aya/README.md)
    - [haskeller-tutorial](https://utensil.github.io/formal-land/aya/haskeller-tutorial.html)
    - [prover-tutorial](https://utensil.github.io/formal-land/aya/prover-tutorial.html)
    - [literate](https://utensil.github.io/formal-land/aya/literate.html)
- [TLA+](./tla/README.md)
    - [pluscal.pdf](https://utensil.github.io/formal-land/tla/pluscal.pdf)

## In scope

- [Coq](https://coq.inria.fr/) ([renaming](https://coq.discourse.group/t/coq-community-survey-2022-results-part-iv-and-itp-paper-announcement/2001) to Rocq): an interactive theorem prover
    - particularly with [math-from-nothing](https://github.com/sudgy/math-from-nothing)
- [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php)
    - particularly with [1lab](https://github.com/the1lab/1lab)
- [Isabelle](https://isabelle.in.tum.de/)
    - [Simple type theory is not too simple: Grothendieck’s schemes without dependent types](https://www.tandfonline.com/doi/full/10.1080/10586458.2022.2062073)
    - [Lie Groups and Algebras](https://www.isa-afp.org/entries/Lie_Groups.html)
    - [Topological Groups](https://www.isa-afp.org/entries/Topological_Groups.html)
- [Metamath](http://us.metamath.org/), see also [Metamath-knife](https://github.com/metamath/metamath-knife) (in Rust)
- [Mizar](http://mizar.org/), see also [mizar-rs](https://github.com/digama0/mizar-rs)
- [egg](https://egraphs-good.github.io/), see also [egglog](https://github.com/egraphs-good/egglog) and [lean-egg](https://github.com/marcusrossel/lean-egg)
- [Charon](https://github.com/AeneasVerif/charon): process Rust crates and convert them into files easy to handle by program verifiers
- [Kani](https://github.com/model-checking/kani): a bit-precise model checker for Rust, particularly useful for verifying unsafe code blocks
- [Aneris](https://github.com/logsem/aneris): a higher-order distributed concurrent separation logic for developing and verifying distributed systems, built on Iris and Coq
- [Dafny](https://dafny.org/): a verification-aware programming language that has native support for recording specifications and is equipped with a static program verifier, used by [Cedar](https://github.com/cedar-policy) before [porting to Lean 4](https://github.com/cedar-policy/rfcs/blob/main/text/0032-port-formalization-to-lean.md)
- [F*](https://fstar-lang.org/): a general-purpose proof-oriented programming language, supporting both purely functional and effectful programming. It compiles to OCaml, and C.
- [Z3](https://github.com/Z3Prover/z3): an efficient SMT (Satisfiability Modulo Theories) solver with specialized algorithms for solving background theories.

## Related (mostly CAS)

- [GAP - Groups, Algorithms, Programming](https://github.com/gap-system/gap): a System for Computational Discrete Algebra
- [Macaulay2](https://www.macaulay2.com/): a software system devoted to supporting research in algebraic geometry and commutative algebra
- [Singular](https://www.singular.uni-kl.de/): a computer algebra system for polynomial computations, with special emphasis on commutative and non-commutative algebra, algebraic geometry, and singularity theory
- [GiNaC](https://www.ginac.de/): a C++ library for symbolic mathematical calculations
- [FLINT](https://flintlib.org/): a C library for doing number theory, which incooperates [Calcium](https://fredrikj.net/calcium/) that provides exact computation with real and complex numbers.

