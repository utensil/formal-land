-- import Std.Tactic.Rcases
-- import Mathlib.Tactic.Cases
-- import Mathlib.Tactic.Use
import Mathlib.Logic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Use

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/rcases.20vs.20cases

-- ## Understanding `rintro` for 1 pattern

-- using `rintro`
example (p: Nat → Prop) : (∃ a, p a) → (∃ b, p b) → (∃ c, p c) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  use a

-- break `rintro` into `intro`s and `obtain`s
example (p: Nat → Prop) : (∃ a, p a) → (∃ b, p b) → (∃ c, p c) := by
  intro h1
  intro h2
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use a

-- rewrite `obtain` to `cases'`
example (p: Nat → Prop) : (∃ a, p a) → (∃ b, p b) → (∃ c, p c) := by
  intro h1
  intro h2
  cases' h1 with a ha
  cases' h2 with a ha
  use a

-- ## Understanding `rintro` for 1+ patterns

-- using `rintro`
example (p: Nat → Nat → Prop) : (∃ a, (∃ b, p a b)) → (∃ c, (∃ d, p c d)) := by
  rintro ⟨a, ⟨b, hb⟩⟩
  use a
  use b

-- break `rintro` into `intro`s and `cases'`s
example (p: Nat → Nat → Prop) : (∃ a, (∃ b, p a b)) → (∃ c, (∃ d, p c d)) := by
  intro h
  cases' h with a ha
  cases' ha with b hb
  use a
  use b

-- collapse `cases'`s into a single `rcases`
example (p: Nat → Nat → Prop) : (∃ a, (∃ b, p a b)) → (∃ c, (∃ d, p c d)) := by
  intro h
  rcases h with ⟨a, ⟨b, hb⟩⟩
  use a
  use b

-- rewrite `rcases` to `obtain` then look at `rintro` above again
example (p: Nat → Nat → Prop) : (∃ a, (∃ b, p a b)) → (∃ c, (∃ d, p c d)) := by
  intro h
  obtain ⟨a, ⟨b, hb⟩⟩ := h
  use a
  use b

namespace Foo

#check eq_or_ne

variable (p q r: Prop)

example (h: p ∨ q) : q ∨ p := by
  obtain (hp | hq) := h
  . exact Or.inr hp
  . exact Or.inl hq

example (h: p ∧ q) : q ∧ p := by
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

example (h: (p ∨ q) ∧ r) : r ∧ (q ∨ p) := by
  obtain ⟨hp | hq, hr⟩ := h
  . exact ⟨hr, Or.inr hp⟩
  . exact ⟨hr, Or.inl hq⟩

example (h: p ∨ q) : q ∨ p := by
  cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h
