import Mathlib

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/API.2Ftactic.20for.20subspace.20topology

example (s t : Set ℝ) (hs : IsClosed s) : closure (s ∩ t) ∩ t ⊆ s ∩ t := by
  simp only [Set.subset_inter_iff, Set.inter_subset_right, and_true]
  intro x hx
  obtain ⟨hxst, _hxt⟩ := hx
  have hsub : closure (s ∩ t) ⊆ s := by
    rw [propext (IsClosed.closure_subset_iff hs)]
    exact Set.inter_subset_left
  exact hsub hxst

example (s t : Set ℝ) (hst: IsClosed (s ∩ t)) : closure (s ∩ t) ∩ t ⊆ s ∩ t := by
  simp only [Set.subset_inter_iff, Set.inter_subset_right, and_true]
  intro x hx
  obtain ⟨hxst, _hxt⟩ := hx
  have _hclosed : IsClosed (closure (s ∩ t)) := by
    exact isClosed_closure
  have hsub : (s ∩ t) ⊆ s := by exact Set.inter_subset_left
  have hsub'' : closure (s ∩ t) ⊆ (s ∩ t) := by
    rw [propext (IsClosed.closure_subset_iff hst)]
  exact hsub (hsub'' hxst)
  done

example (s t : Set ℝ) (hst: IsClosed (s ∩ t)) : closure (s ∩ t) ∩ t ⊆ s ∩ t := by
  simp only [Set.subset_inter_iff, Set.inter_subset_right, and_true]
  intro x hx
  obtain ⟨hxst, _⟩ := hx
  have h : (s ∩ t) ⊆ s := by exact Set.inter_subset_left
  have hsub : closure (s ∩ t) ⊆ (s ∩ t) := by
    rw [propext (IsClosed.closure_subset_iff hst)]
  exact h (hsub hxst)
  done

variable {X} [TopologicalSpace X]

def restrict (A : Set X) : Set X → Set A := fun B ↦ {x | ↑x ∈ B}

-- @[simp]
-- lemma restrict_coe {A : Set X} ( C : Set X) : (Subtype.val ⁻¹' C : Set A) = (restrict A C) := rfl

example (s t : Set X) : restrict t s = (Subtype.val ⁻¹' s : Set t) := by
  ext x
  simp [restrict]


example (s t : Set X) (hs : IsClosed (restrict t s)) : closure (s ∩ t) ∩ t ⊆ s ∩ t := by
  simp only [Set.subset_inter_iff, Set.inter_subset_right, and_true]
  intro x hx
  obtain ⟨hxst, _⟩ := hx
  have h : (s ∩ t) ⊆ s := by exact Set.inter_subset_left
  have hsub : closure (restrict t s) ⊆ (restrict t s) := by rwa [IsClosed.closure_subset_iff]
  have hsub' : (restrict t s) ⊆ closure (restrict t s) := by exact subset_closure
  have hsub'' : (s ∩ t) ⊆ closure (s ∩ t) := by exact subset_closure
  have he : (restrict t s) = closure (restrict t s) := by exact Set.Subset.antisymm hsub' hsub
  -- have hq : (restrict t s) ⊆ t := sorry
  obtain ⟨y, ⟨hy, hy'⟩⟩ := hs
  -- have h' : (s ∩ t) ⊆ (restrict t s) := by
  --   rw?
  sorry
  done

-- example (s t : Set X) (hs : IsClosed (Subtype.val ⁻¹' s : Set t)) : closure (s ∩ t) ∩ t ⊆ s ∩ t := by
--   suffices : closure (Subtype.val ⁻¹' s : Set t) ⊆ (Subtype.val ⁻¹' s : Set t)
--   · convert Set.image_subset Subtype.val this <;> simp [embedding_subtype_val.closure_eq_preimage_closure_image]
--   rwa [IsClosed.closure_subset_iff]

variable {α : Type u} {β : Type v}

def image    (f : α → β) (s : Set α) : Set β := {f x | x ∈ s}
def preimage (f : α → β) (s : Set β) : Set α := { x | f x ∈ s }


variable  (s t : Set X) in
#check IsClosed (Set.preimage Subtype.val s)

example (s t : Set X) (hs : IsClosed (Subtype.val ⁻¹' s : Set t)) : closure (s ∩ t) ∩ t ⊆ s ∩ t := by
  sorry
  done


-- example (s t : Set ℝ) (hs : IsOpen s): closure (s ∩ t) ∩ t ⊆ s ∩ t := by
--   simp only [Set.subset_inter_iff, Set.inter_subset_right, and_true]
--   intro x hx
--   obtain ⟨hxst, hxt⟩ := hx
--   rw [mem_closure_iff] at hxst
--   have h := hxst s hs
--   have he : (s ∩ (s ∩ t)) = s ∩ t := by
--     simp only [Set.inter_eq_right, Set.inter_subset_left]
--   have hne (hu: Set.Nonempty (s ∩ t)) : Set.Nonempty (s ∩ (s ∩ t)) := by
--     rw [he]
--     exact hu

--   done

-- open Set

-- example (s t : Set ℝ) : closure (s ∩ t) ∩ t ⊆ s ∩ t := by
--   rw [← Subtype.image_preimage_val, ← Subtype.image_preimage_val,
--     image_subset_image_iff Subtype.val_injective]
--   intros t ht
--   rw [mem_preimage, ← closure_subtype] at ht
--   revert ht t
--   apply IsClosed.closure_subset
