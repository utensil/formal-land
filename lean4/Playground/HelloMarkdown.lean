/-!

# Hello

## Inspecting Lean

-/
#eval Lean.versionString

#eval Lean.versionStringCore

#eval Lean.toolchain

#eval Lean.origin

#eval Lean.githash

/-!

## Proofs

-/
theorem test (p q : Prop) (hp : p) (hq : q): p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    apply And.intro
    . exact hq
    . exact hp
  . intro h
    apply And.intro
    . exact hp
    . exact hq
