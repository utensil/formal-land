/-
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/category.20of.20sets
-/
import init.function
import category_theory.category
import category_theory.types
import category_theory.full_subcategory
import category_theory.sums.basic
import category_theory.products.basic
import algebra.category.Group

universes u v

-- -- one-to-one
-- #check function.injective
-- -- onto
-- #check function.surjective

-- #check function.bijective

-- #check category_theory.mono

-- #check category_theory.epi

open category_theory

-- def Set := induced_category _ (λ A : bundled set, A.1)

-- -- structure Set
-- -- (carrier: Type u)
-- -- (map: carrier → carrier)

variables (X : Type u)

/-
preorder.small_category (set X) : small_category (set X)
-/
#check (by apply_instance : category (set X))

instance Set.category : category (set X) :=
{ hom  := λ A B, A → B,
  id   := λ S s, s,
  comp :=  λ _ _ _ f g, g ∘ f }

-- set_option trace.class_instances true

-- def Set.as_hom {A : set X} (a : X) : A ⟶ A := 

-- lemma Set.as_hom_injective {A : set X} [category A] : function.injective (@as_hom A) := sorry
-- λ h k w, by convert congr_arg (λ k : (AddCommGroup.of ℤ) ⟶ G, (k : ℤ → G) (1 : ℤ)) w; simp

lemma Set.injective_of_mono {A B : set X} (f : A ⟶ B) [mono f] : function.injective f :=
begin  
  assume a₁ a₂ h,
  let α₁ : A → A := λ _, a₁,
  let α₂ : A → A := λ _, a₂,
  let hom_α₁ := as_hom α₁,
  let hom_α₂ := as_hom α₂,
  have t0 : hom_α₁ ≫ f = hom_α₂ ≫ f :=
  begin
    ext x',
    cases x',
    cases a₁,
    cases a₂,
    dsimp at *,
    solve_by_elim,
  end,
  have t1 : hom_α₁ = hom_α₂ := (cancel_mono f).mp t0,
  have t2 : α₁ = α₂ := by assumption,
  have t3 : α₁ a₁ = α₂ a₁ := by rw t2,
  have t4 : α₁ a₁ = a₁ := rfl,
  have t5 : α₂ a₁ = a₂ := rfl,
  assumption,
end
/-
Mathematical Physics (Chicago Lectures in Physics)
by Robert Geroc
-/

-- Chap. 2

-- theorem 1
#check mono_iff_injective
-- theorem 2
#check epi_iff_surjective
-- theorem 3
#check mono_comp
#check epi_comp
-- theorem 4
#check category_theory.uniform_prod
-- theorem 5
#check category_theory.sum
-- theorem 6
#check prod.braiding
#check sum.swap.equivalence



