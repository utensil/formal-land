import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

universe u1 u2 u3

-- #help tactic
-- https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md

-- https://github.com/madvorak/lean4-tactics

/-

  The following follows Lean series on writing tactics
  
  https://www.vladasedlacek.cz/en/posts/lean-02-demo

-/

class incidence_geometry :=
(point : Type u1)
(line : Type u2)
(circle : Type u3)

(length : point → point → ℝ)
(B : point → point → point → Prop) -- Betweenness

(length_nonneg : ∀ (a b : point), 0 ≤ length a b)
(length_symm : ∀ (a b : point), length a b = length b a)
(length_eq_zero_iff : ∀ {a b : point}, length a b = 0 ↔ a = b)
(length_sum_of_B : ∀ {a b c : point},
   B a b c → length a b + length b c = length a c)
(ne_12_of_B : ∀ {a b c : point}, B a b c → a ≠ b )
(ne_13_of_B : ∀ {a b c : point}, B a b c → a ≠ c )
(ne_23_of_B : ∀ {a b c : point}, B a b c → b ≠ c )

variable [i : incidence_geometry]
open incidence_geometry

lemma len_pos_of_neq₁ (ab : a ≠ b) : 0 < length a b := by
  have h₁ : length a b ≠ 0 := by
    by_contra h
    rw [length_eq_zero_iff] at h
    exact (absurd h ab)
  have h₂ : 0 ≤ length a b := length_nonneg a b
  exact lt_of_le_of_ne h₂ h₁.symm

-- #find |- ?a ≠ ?b

lemma len_pos_of_neq₂ (ab : a ≠ b) : 0 < length a b := by
  have h1 : length a b ≠ 0 := length_eq_zero_iff.not.mpr ab
  have h2 := length_nonneg a b
  exact lt_of_le_of_ne h2 h1.symm

lemma len_pos_of_neq₃ (ab : a ≠ b) : 0 < length a b := by
  have h1 : length a b ≠ 0 := length_eq_zero_iff.not.mpr ab
  have h2 := length_nonneg a b
  exact lt_of_le_of_ne h2 h1.symm

lemma len_pos_of_neq₄ (ab : a ≠ b) : 0 < length a b := by
  have h1 : length a b ≠ 0 := length_eq_zero_iff.not.mpr ab
  have h2 := length_nonneg a b
  exact lt_of_le_of_ne h2 h1.symm

lemma len_pos_of_neq (ab : a ≠ b) : 0 < length a b := len_pos_of_neq₂ ab

theorem length_sum_perm_of_B₁ (Babc : B a b c) :
      0 < length a b ∧ 0 < length b a := by
    have ab : a ≠ b := ne_12_of_B Babc
    have ab_pos : 0 < length a b := len_pos_of_neq ab
    constructor
    . exact ab_pos
    . rw [length_symm] at ab_pos
      exact ab_pos

theorem length_sum_perm_of_B₂ (Babc : B a b c) :
      0 < length a b ∧ 0 < length b a := by
      constructor
      . exact ne_12_of_B Babc |> len_pos_of_neq
      . exact ne_12_of_B Babc |> (length_symm a b ▸ len_pos_of_neq)

theorem length_sum_perm_of_B₃ (Babc : B a b c) : 0 < length a b ∧ 0 < length b a := by
   simp only [ne_eq, ne_12_of_B Babc, len_pos_of_neq, length_symm]
