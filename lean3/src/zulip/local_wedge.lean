/-
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Redefine.20precedence.20of.20.60infix.60
-/
import tactic.localized
open tactic

universe u

namespace domain

class has_wedge (α : Type u) := (wedge : α → α → α)

localized "infix ∧:70 := has_wedge.wedge" in domain

end domain

namespace userland

open domain
open_locale domain

-- I'm being lazy here to define a dummy wedge
instance nat.to_has_wedge : has_wedge ℕ := {
  wedge := (*)
}

lemma dummy : 2 ∧ 3 = 6 := rfl

/-
failed to synthesize type class instance for
⊢ has_wedge Prop
-/
lemma dummy' : (2 ∧ 3 = 6) ∧ (2 ∧ 9 = 18) := sorry

end userland

-- \curlywedge ⋏
-- \curlyvee ⋎
