/-
  https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/barber.20paradox/near/206937100
-/

import tactic

variables (Man : Type) (shaves : Man → Man → Prop)

theorem NoSuchBarber ( h : ∃ barber : Man,  ∀ m : Man, shaves barber m ↔ ¬ shaves m m )
: false :=
begin
  -- from the existence of such a barber, we obtain a barber and the associated hypothesis
  obtain ⟨barber, barber_shaves_only_who_doesnt_self_shave⟩ := h, 
  -- apply the associated hypothesis to the barber (as a customer)
  have self_shaving_dilemma := barber_shaves_only_who_doesnt_self_shave barber,
  -- apply `(a ↔ ¬a) → false` to `shaves barber barber` as `a`
  have dilemma_implies_false := (iff_not_self (shaves barber barber)).mp,
  -- -- apply the theorem "dilemma implies false" to the fact that
  -- -- we have proven the self-shaving dilemma
  exact dilemma_implies_false self_shaving_dilemma,
  -- solve_by_elim,
end

