/-
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/rewrite.20le.2Eantisymm.20from.20Lean.202
-/

import tactic
import tactic.lint

open int

theorem le.antisymm : ∀ {a b : ℤ}, a ≤ b → b ≤ a → a = b :=
begin
assume a b : ℤ, assume (H₁ : a ≤ b) (H₂ : b ≤ a),
obtain ⟨n, Hn⟩ : ∃ n : ℕ, a + n = b := int.le.dest H₁,
obtain ⟨m, Hm⟩ : ∃ m : ℕ, b + m = a := int.le.dest H₂,
have H₃ : a + of_nat (n + m) = a + 0, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : rfl
      ... = a + (n + m)                     : by rw of_nat_eq_coe
      ... = a + n + m                       : by rw add_assoc
      ... = b + m                           : by rw Hn
      ... = a                               : Hm
      ... = a + 0                           : by rw add_zero,
have H₄ : of_nat (n + m) = of_nat 0, from add_left_cancel H₃,
have H₅ : n + m = 0,                 from of_nat.inj H₄,
have h₆ : n = 0,                     from nat.eq_zero_of_add_eq_zero_right H₅,
show a = b, from
  calc
    a = a + 0    : by simp_rw [add_zero]
  ... = a + n    : by simp_rw [h₆, int.coe_nat_zero]
  ... = b        : Hn
end

