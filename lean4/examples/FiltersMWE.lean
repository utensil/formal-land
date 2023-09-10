import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Explode

theorem Filter.ext_iff' (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  simp only [filter_eq_iff, Set.ext_iff, Filter.mem_sets]

theorem Filter.ext_iff'' (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
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

#explode Filter.ext_iff'

#explode Filter.ext_iff''

def f : α → α :=
  fun f =>
    let s := 1
    sorry
