# Lean 4 Playground

## Setup

### Install Lean 4 and Configure it

Just trigger it following [Quickstart in Lean 4 Manual](https://leanprover.github.io/lean4/doc/quickstart.html) with the help from the VSCode extension for Lean 4.

### Create a Lean 4 project

```bash
lake init project_name
lake build

lake env lean --run examples/Hello.lean
```

Note: On windows, ensure that the Lean 4 is added to `PATH` by a hard restart of VSCode.
