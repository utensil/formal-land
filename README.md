# Lean Playground

## Setup

### Install Lean and Configure it

```
curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh
```

```
elan toolchain install stable
elan toolchain install nightly
elan default nightly
```

### Install Lean extension for VS Code

Visit https://marketplace.visualstudio.com/items?itemName=jroesch.lean

### Experiment!

```
lean hello.lean
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