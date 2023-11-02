import Mathlib

open Real

#check π

#check rexp 1

#check Irrational (rexp 1 + π)

example (a b c : ℕ) : a + b * c = c * b + a := by ring

example (a b c : ℕ) : a + b * c = c * b + a := by show_term ring

example : 24 ^ 9 < 9 ^ 25 := by show_term norm_num

example (a b c : ℕ) : a + b * c = c * b + a := by
  rw [Nat.add_comm, @Nat.add_right_cancel_iff, Nat.mul_comm]

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity

noncomputable def chooseNat (h : ∃ (x : ℕ), x > 4) : ℕ := Nat.find h

noncomputable def chooseNat' (h : ∃ (x : ℕ), x > 4) : ℕ := Exists.choose h

variable {f : ℝ → ℝ}

def fnUB (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

def fnHasUB (f : ℝ → ℝ) := ∃ a, fnUB f a

example (h : ∀ a, ∃ x, f x > a) : ¬ fnHasUB f := by
  simp only [fnHasUB, fnUB] at *
  rintro ⟨a, ha⟩
  specialize h a
  obtain ⟨b, hb⟩ := h
  specialize ha b
  rw [<- not_lt] at ha
  contradiction
