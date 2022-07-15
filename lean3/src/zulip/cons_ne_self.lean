/-
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/(list.2Econs.20a.20l).20.E2.89.A0.20l
-/
import tactic

universe u

example {α : Type u} (a : α) (l : list α) : (list.cons a l) ≠ l := begin
  induction l,
  { simp },
  simp only [not_and, ne.def],
  rintro ⟨⟩,
  exact l_ih,
end

-- example {α : Type u} (a : α) (l : list α) : (list.cons a l) ≠ l := begin
--   refl <|> ac_refl <|> assumption <|> squeeze_simp <|> cc <|> ring <|> nlinarith <|> norm_cast <|> norm_num <|> tauto <|> trivial <|> hint <|> suggest <|> tidy? <|> finish <|> clarify <|> safe <|> library_search!
-- end

example {α : Type u} (a : α) (l : list α) : (list.cons a l) ≠ l := begin
  rw ne.def,
  induction l,
  {
    simp only [not_false_iff],
  },
  {
    simp only [not_and],
    intro h,
    cases h,
    assumption,
  }
end

example {α} (a : α) (l : list α) : list.cons a l ≠ l :=
begin
  apply mt (congr_arg list.length),
  apply ne_of_gt,
  apply nat.lt_succ_self l.length,
end

example {α} (a : α) (l : list α) : list.cons a l ≠ l :=
begin
  apply mt (congr_arg list.length),
  apply ne_of_gt,
  apply nat.lt_succ_self l.length,
end

example (a : ℕ) (l : list ℕ) : list.cons a l ≠ list.nil
| h := by cases h

-- set_option trace.eqn_compiler.elim_match true

namespace hidden
open list

-- https://github.com/leanprover-community/mathlib/issues/3584
lemma cons_ne_self' {α : Type u} : ∀ (a : α) (l : list α), (cons a l) ≠ l
| a nil := cons_ne_nil a nil
| a (h :: t) := cons_ne_self' h t ∘ tail_eq_of_cons_eq

/-
equation compiler failed to create auxiliary declaration '_example._main._pack.equations._eqn_2'
nested exception message:
invalid equation lemma, unexpected form
-/
-- example {α : Type u} : ∀ (a : α) (l : list α), (cons a l) ≠ l
-- | a nil := by simp
-- | a (cons h t) := by solve_by_elim

/-
failed to prove recursive application is decreasing, well founded relation
  @has_well_founded.r (Σ' (a : α), list α)
    (@psigma.has_well_founded α (λ (a : α), list α) (@has_well_founded_of_has_sizeof α (default_has_sizeof α))
       (λ (a : α), @has_well_founded_of_has_sizeof (list α) (@list.has_sizeof α (default_has_sizeof α))))
The nested exception contains the failure state for the decreasing tactic.
nested exception message:
invalid apply tactic, failed to unify
  0 < 0
with
  ?m_1 < ?m_1 + ?m_2
state:
α : Type u,
cons_ne_self : ∀ (_p : Σ' (a : α), list α), _p.fst :: _p.snd ≠ _p.snd,
a h : α,
t : list α,
a : α,
l : list α
⊢ 0 < 0
-/
-- lemma cons_ne_self'' {α : Type u} : ∀ (a : α) (l : list α), (cons a l) ≠ l
-- | a nil := by simp
-- | a (cons h t) := by simp [cons_ne_self'']
-- using_well_founded {
--   dec_tac := well_founded_tactics.default_dec_tac
-- }

lemma cons_ne_self {α : Type u} : ∀ (a : α) (l : list α), (cons a l) ≠ l
| a nil := by simp
| a (cons h t) := by simp [cons_ne_self h t]

end hidden