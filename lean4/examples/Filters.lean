import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite

set_option linter.unusedVariables false
set_option autoImplicit false

/-!

Note: This file is adapted from [bridgekat/filter-game](https://github.com/bridgekat/filter-game)

-/
namespace FilterGame
variable {α : Type _}

/-!

# Filters

Given a type `α`, a filter is a collection of sub**sets** of `α` which

- contains the whole set (the **univ**ersal set is a **mem**ber of **sets**) 
- upward closed (**superset**s are **mem**bers of **sets**)
- closed under intersections (**inter**sections are **mem**bers of **sets**)
-/
structure Filter (α : Type _) where
  sets                    : Set (Set α)
  univ_mem_sets           : Set.univ ∈ sets
  superset_mem_sets {s t} : s ∈ sets → s ⊆ t → t ∈ sets
  inter_mem_sets {s t}    : s ∈ sets → t ∈ sets → s ∩ t ∈ sets

/-!
## Notation `s ∈ f`

If we have a filter `f`, it is more convenient to write `s ∈ f` for `s ∈ f.sets`.

To define the notation, we simply provide an instance for the typeclass `Membership`
which has defined notation `∈` on it.

Providing an instance, is providing all fields of the class, some are data-like, 
some are function-like, and some are property-like.

We need to provide the data or function implementation for the first two kinds,
prove the property for the last kind.

Here we only need to provide a function.
-/
instance : Membership (Set α) (Filter α) := {
  mem := fun s f ↦ s ∈ f.sets
}

/-!
  To simplify, we can surround the ordered fields with `⟨` and `⟩`, seperated by `,`.
-/
instance : Membership (Set α) (Filter α) :=
  ⟨fun s f ↦ s ∈ f.sets⟩

/-!
  Now that `∈` is defined.

  We prove an obviously true statement.
-/
example (f : Filter α) (s : Set α) : s ∈ f ↔ s ∈ f := by
  exact Iff.rfl

/-!
  We then prove its propositional equality, and make it available for `simp`.
-/
@[simp]
theorem Filter.mem_def (f : Filter α) (s : Set α) : s ∈ f ↔ s ∈ f.sets := by
  exact Iff.rfl

/-!
## The equality between filters

If `f.sets` and `g.sets` are equal, we consider `f` and `g` to be equal, too.

-/
@[simp]
theorem Filter.eq_def (f g : Filter α) : f = g ↔ f.sets = g.sets := by
  apply Iff.intro
  . intro h
    rw [h]
  . intro h
    induction f
    induction g
    rw [mk.injEq]
    assumption

theorem Filter.ext_iff' (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  simp only [eq_def, Set.ext_iff, mem_def]

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
    rw [eq_def]
    rw [Set.ext_iff]
    intro s
    specialize set_mem_iff s
    simp only [<-mem_def]
    exact set_mem_iff
    
      


    
    

    





