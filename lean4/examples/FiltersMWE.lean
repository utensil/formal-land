import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Explode

theorem Filter.ext_iff₁ (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  simp only [filter_eq_iff, Set.ext_iff, Filter.mem_sets]

theorem Filter.ext_iff₂ (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  apply Iff.intro
  . intro f_eq_g
    intro s
    apply Iff.intro
    . intro s_mem_f
      rw [<-f_eq_g]
      exact s_mem_f
    . intro s_mem_g
      rw [f_eq_g]
      exact s_mem_g
  . intro set_mem_iff
    rw [filter_eq_iff]
    rw [Set.ext_iff]
    intro s
    specialize set_mem_iff s
    exact set_mem_iff

theorem Filter.ext_iff₃ (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  calc
    (f = g) ↔ (f.sets = g.sets)                           := by rw [filter_eq_iff]
          _ ↔ ∀ (x : Set α), x ∈ f.sets ↔ x ∈ g.sets      := by rw [Set.ext_iff]
          _ ↔ ∀ (x : Set α), x ∈ f ↔ x ∈ g                := by simp_rw [Filter.mem_sets]

theorem Filter.ext_iff₄ (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  have mem_sets_eq_mem: ∀ (fg : Filter α) (x : Set α), (x ∈ fg.sets) = (x ∈ fg) := by
    intros fg x
    rw [Filter.mem_sets]
  calc
    (f = g) ↔ (f.sets = g.sets)                           := by rw [filter_eq_iff]
          _ ↔ ∀ (x : Set α), x ∈ f.sets ↔ x ∈ g.sets      := by rw [Set.ext_iff]
          _ ↔ ∀ (x : Set α), x ∈ f ↔ x ∈ g                := by
            conv_lhs =>
              intro x
              rw [mem_sets_eq_mem f]
              rw [mem_sets_eq_mem g]

-- 19
#explode Filter.ext_iff₁

-- 38
#explode Filter.ext_iff₂

-- 31
#explode Filter.ext_iff₃

-- 60
#explode Filter.ext_iff₄
