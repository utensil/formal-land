/-

Test an exotic have syntax, from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Behavior.20of.20'have'.20tactic.20changing.20with.20imports

-/
theorem test_have3 (p q : Prop) : ((p ∧ ¬q) ∨ (q ∧ ¬p)) ↔ ((p ∨ q) ∧ ¬(p ∧ q)) := by
  have my_p (h₁ : ((p ∧ ¬q) ∨ (q ∧ ¬p))) : (p ∨ q) ∧ ¬(p ∧ q) := by
    sorry
  sorry


