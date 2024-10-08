# Lean 4 Playground

[![Lean 4 Playground](https://github.com/utensil/formal-land/actions/workflows/lean4.yml/badge.svg)](https://github.com/utensil/formal-land/actions/workflows/lean4.yml)

See it in action [here](https://utensil.github.io/formal-land/lean4/).

## Install Lean 4 and Configure it

Just trigger it following [Quickstart in Lean 4 Manual](https://leanprover.github.io/lean4/doc/quickstart.html) with the help from the VSCode extension for Lean 4.

## Run tests

```bash
lake test
```

See `scripts/test` for more details about running individual tests, and test options.

## Minimalize a file

Check out `Playground/Zulip/CodeActions.lean`.

## Plans

Explore the following:

- [SciLean](https://github.com/lecopivo/SciLean)
- [HepLean](https://github.com/HEPLean/HepLean)
- [cedar-spec](https://github.com/cedar-policy/cedar-spec)
- [SampCert](https://github.com/leanprover/SampCert)
- [Lean-MLIR](https://github.com/opencompl/lean-mlir)
- [verbose-lean4](https://github.com/PatrickMassot/verbose-lean4)
- [Duper](https://github.com/leanprover-community/duper)
- Games in Lean
  - [lean4-maze](https://github.com/dwrensha/lean4-maze)
  - [TwoFX/sudoku](https://github.com/TwoFX/sudoku)
  - Rubik's cubes
    - [vihdzp/rubik-lean4](https://github.com/vihdzp/rubik-lean4)
    - [kendfrey/rubiks-cube-group](https://github.com/kendfrey/rubiks-cube-group)
    - [gshartnett/rubiks-clifford-synthesis](https://github.com/gshartnett/rubiks-clifford-synthesis)

Maybe each needs a separate Lean 4 project so these dependencies can be upgraded separately.
