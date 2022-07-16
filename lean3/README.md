# Lean 3 Playground

## Setup

### Install Lean and Configure it

On *nix:

```bash
# On Mac
# brew install gmp coreutils

yes 1|curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | bash -s -- -y
```

On Windows:

Download and run `elan-init.exe` from https://github.com/Kha/elan/releases/tag/v0.8.0

Then on both:

```bash
elan toolchain install stable
elan default stable
```

### Install Lean extension for VS Code

Visit https://marketplace.visualstudio.com/items?itemName=jroesch.lean

### Install Mathlib Tools

```bash
pip install mathlibtools
```

### Install Lean formatter

```bash
# pip install -U git+https://github.com/utensil-contrib/format_lean.git@working
pip install -U https://github.com/leanprover-community/format_lean/archive/master.zip
```

### Download dependencies

```bash
leanpkg configure
# leanproject get-mathlib-cache
```

### Experiment!

```bash
lean src/hello.lean
```

```lean
a : ℤ
f : ℤ → ℤ
λ (x : ℤ), g (f (g a x)) (g x b) : ℤ → ℤ
λ (x : ℤ), g (f (g a x)) (g x b) : ℤ → ℤ
trool.maybe : trool
inductive ℕat : Type
constructors:
ℕat.zero : ℕat
ℕat.succ : ℕat → ℕat
List.nil : List ?M_1
List.cons : ?M_1 → List ?M_1 → List ?M_1
List.nil : Π {α : Type}, List α
List.cons : Π {α : Type}, α → List α → List α
list.nil : list ?M_1
λ (α : Type) (x : α) (xs : list α), x :: xs : Π (α : Type), α → list α → list α
λ (α : Type) (x_1 x_ooo x_n : α), [x_1, x_ooo, x_n] : Π (α : Type), α → α → α → list α
list.nil : list ?M_1
λ (Animal : Type) (cat : Animal) (cats : list Animal), cat :: cats :
  Π (Animal : Type), Animal → list Animal → list Animal
λ (Animal : Type) (cat_1 cat_ooo cat_n : Animal), [cat_1, cat_ooo, cat_n] :
  Π (Animal : Type), Animal → Animal → Animal → list Animal
```

```bash
cd src
format_lean --inpath hello.lean --outdir build
# open build/hello.html
```

### Work with Lean 4 and Lean 3 side by side

* Disable Lean 4 extension for Lean 3 projects (in extension workspace settings)
* Check `elan toolchain list`