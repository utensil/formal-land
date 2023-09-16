# Lean 4 Playground

## Setup

### Install Lean 4 and Configure it

#### Linux

Just trigger it following [Quickstart in Lean 4 Manual](https://leanprover.github.io/lean4/doc/quickstart.html) with the help from the VSCode extension for Lean 4.

#### Mac

Follow [How to install Lean 4 on MacOS](https://leanprover-community.github.io/install/macos.html), i.e. run

```
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_macos.sh)" && source ~/.profile
```

### Create a Lean 4 project

Follow [Lean projects](https://leanprover-community.github.io/install/project.html) with [updates here](https://leanprover.zulipchat.com/#narrow/stream/113486-announce/topic/First.20official.20release/near/389827646), i.e. run

```bash
lake +leanprover/lean4:stable new my_project
cd my_project
lake exe cache get
lake build
```

Note: On windows, ensure that the Lean 4 is added to `PATH` by a hard restart of VSCode.



