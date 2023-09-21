import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.Explode

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
    
theorem Filter.ext_iff₁ (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  simp only [eq_def, Set.ext_iff, mem_def]

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
    rw [eq_def]
    rw [Set.ext_iff]
    intro s
    specialize set_mem_iff s
    exact set_mem_iff

theorem Filter.ext_iff₃ (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  calc
    (f = g) ↔ (f.sets = g.sets)                           := by rw [eq_def]
          _ ↔ ∀ (x : Set α), x ∈ f.sets ↔ x ∈ g.sets      := by rw [Set.ext_iff]
          _ ↔ ∀ (x : Set α), x ∈ f ↔ x ∈ g                := by simp_rw [mem_def]

theorem Filter.ext_iff₄ (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  have mem_sets_eq_mem: ∀ (fg : Filter α) (x : Set α), (x ∈ fg.sets) = (x ∈ fg) := by
    intros fg x
    rw [mem_def]
  calc
    (f = g) ↔ (f.sets = g.sets)                           := by rw [eq_def]
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

def f : α → α :=
  fun f =>
    let s := 1
    sorry

/-!

## Trivial lemmas

These lemmas directly follow from the definiton of the filters:
-/
theorem Filter.univ_mem (f : Filter α) : Set.univ ∈ f := by
  exact f.univ_mem_sets

theorem Filter.superset_mem {f : Filter α} {s t : Set α} (hs : s ∈ f) (h : s ⊆ t) : t ∈ f := by
  exact f.superset_mem_sets hs h

theorem Filter.inter_mem {f : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f := by
  exact f.inter_mem_sets hs ht

theorem Filter.inter_mem₁ {f : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f := f.inter_mem_sets hs ht

theorem Set.mem_iff (p : α → Prop) (y : α) : y ∈ {x : α | p x} ↔ p y := by
  exact Iff.rfl

/-！

## Examples of filters

-/

example : Filter α := {
  sets := Set.univ
  univ_mem_sets := by
    exact Set.mem_univ Set.univ
  superset_mem_sets := by
    intros s t
    intros «s ∈ univ» «s ⊆ t»
    exact Set.mem_univ t
  inter_mem_sets := by
    intros s t
    intros «s ∈ univ» «t ∈ univ»
    exact Set.mem_univ (s ∩ t)
}

/-！

or, succinctly:

-/

example : Filter α := {
  sets := Set.univ
  univ_mem_sets := by
    apply Set.mem_univ
  superset_mem_sets := by
    intros
    apply Set.mem_univ
  inter_mem_sets := by
    intros
    apply Set.mem_univ
}

/-!
Hint: `rw` using `Set.mem_iff` to unfold the set-builder notation.
Mathlib lemmas `Set.univ_subset_iff` and `Set.inter_self` can be useful here.

Use simp? rw? exact? apply? aesop? to get hints.

-/
example : Filter α := {
  sets := {s : Set α | s = Set.univ}
  univ_mem_sets := by
    rw [Set.mem_iff]
  superset_mem_sets := by
    simp_rw [Set.mem_iff]
    intros s t «s = univ» «s ⊆ t»
    apply Set.univ_subset_iff.mp
    rw [<-«s = univ»]
    exact «s ⊆ t»
  inter_mem_sets := by
    simp_rw [Set.mem_iff]
    intros s t «s = univ» «t = univ»
    rw [«s = univ», «t = univ»]
    exact Set.inter_self Set.univ
}

/-！

or, succinctly:

-/

example : Filter α := {
  sets := {s : Set α | s = Set.univ}
  univ_mem_sets := by
    rw [Set.mem_iff]
  superset_mem_sets := by
    simp_rw [Set.mem_iff]
    intros
    simp_all only [Set.univ_subset_iff]
  inter_mem_sets := by
    simp_rw [Set.mem_iff]
    intros
    simp_all only [Set.inter_self]
}


/-！

The cofinite filter consists of subsets whose complements are finite.

-/
example : Filter α := {
  sets := {s : Set α | Set.Finite sᶜ}
  univ_mem_sets := by
    rw [Set.mem_iff, Set.compl_univ]
    exact Set.finite_empty
  superset_mem_sets := by
    intros s t
    rw [Set.mem_iff]
    intro «sᶜ is finite» «s ⊆ t»
    rw [Set.mem_iff]
    rw [<-Set.compl_subset_compl] at «s ⊆ t»
    exact Set.Finite.subset «sᶜ is finite» «s ⊆ t»
  inter_mem_sets := by
    intros s t
    intro «sᶜ is finite» «tᶜ is finite»
    rw [Set.mem_iff] at «sᶜ is finite»
    rw [Set.mem_iff] at «tᶜ is finite»
    rw [Set.mem_iff]
    rw [Set.compl_inter]
    exact Set.Finite.union «sᶜ is finite» «tᶜ is finite»
}

/-！

or, succinctly:

-/

example : Filter α where
  sets := {s : Set α | Set.Finite sᶜ}
  univ_mem_sets := by
    simp only [Set.mem_iff, Set.compl_univ, Set.finite_empty]
  superset_mem_sets «sᶜ is finite» «s ⊆ t» :=
    «sᶜ is finite».subset <| Set.compl_subset_compl.mpr «s ⊆ t»
  inter_mem_sets := by
    simp_all [Set.mem_iff, Set.compl_inter, Set.Finite.union]

/-!
# Filter bases
-/

/--
Given a type `α`, a filter basis is a collection of sub**sets** of `α` which:

- contains at least one subset (the **sets** collection is **nonempty**),
- intersections of two member subsets include some member subset of the
  collection (**inter**sections include **mem**bers of **sets**).

We represent it in Lean as a new type, which "packages" the collection of
subsets, along with all the properties it should have.
-/
structure Basis (α : Type _) where
  sets                 : Set (Set α)
  sets_nonempty        : ∃ s, s ∈ sets
  inter_mem_sets {s t} : s ∈ sets → t ∈ sets → ∃ u ∈ sets, u ⊆ s ∩ t

/--
If we have a filter basis `b`, it is more convenient to write `s ∈ b` for
`s ∈ b.sets`. We now define this notation.
-/
instance : Membership (Set α) (Basis α) :=
  ⟨fun s b ↦ s ∈ b.sets⟩

/--
The definition of `∈`.
-/
@[simp]
theorem Basis.mem_def (b : Basis α) (s : Set α) : s ∈ b ↔ s ∈ b.sets := by
  exact Iff.rfl

/--
The definition of equality between filter bases.
-/
@[simp]
theorem Basis.eq_def (b c : Basis α) : b = c ↔ b.sets = c.sets := by
  apply Iff.intro
  . intro «b = c»
    rw [«b = c»]
  . intro «b.sets = c.sets»
    cases b
    cases c
    congr

-- 46
#explode Basis.eq_def

theorem Basis.eq_def₁ (b c : Basis α) : b = c ↔ b.sets = c.sets := by
  apply Iff.intro
  . intro «b = c»
    rw [«b = c»]
  . intro «b.sets = c.sets»
    cases b
    cases c
    simp_all only

-- 53
#explode Basis.eq_def₁




