module

public import Foundations.Measure.Embedding.Basic
public import Foundations.Measure.Space.Sum

set_option autoImplicit false

/-!
# Measurable embeddings for direct sums of measurable spaces

This module constructs measurable embeddings for the canonical injections
into a direct sum of measurable spaces. Both injections have measurable
forward images.
-/
namespace Foundations.Measure.MeasurableEmbedding

public section

universe u v

variable {α : Type u} {β : Type v}

/-- Left injection into a measurable sum as a measurable embedding.
Proves that forward images of measurable sets are measurable. -/
@[expose] def inl (left : Space α) (right : Space β) :
    MeasurableEmbedding left (Space.sum left right) where
  function := Sum.inl
  injective := fun _ _ equal => Sum.inl.inj equal
  measurable := MeasurableMap.inl left right
  imageMeasurable := by
    intro region measurable
    constructor
    · have equal : Set.preimage Sum.inl (Set.image (Sum.inl : α → Sum α β) region) =
          region := by
        apply Set.ext
        intro value
        constructor
        · rintro ⟨input, member, equal⟩
          exact Sum.inl.inj equal ▸ member
        · intro member
          exact ⟨value, member, rfl⟩
      rw [equal]
      exact measurable
    · have equal : Set.preimage Sum.inr (Set.image (Sum.inl : α → Sum α β) region) =
          Set.empty := by
        apply Set.ext
        intro value
        constructor
        · rintro ⟨input, _, equal⟩
          cases equal
        · exact False.elim
      rw [equal]
      exact right.empty

/-- Right injection into a measurable sum as a measurable embedding.
Proves that forward images of measurable sets are measurable. -/
@[expose] def inr (left : Space α) (right : Space β) :
    MeasurableEmbedding right (Space.sum left right) where
  function := Sum.inr
  injective := fun _ _ equal => Sum.inr.inj equal
  measurable := MeasurableMap.inr left right
  imageMeasurable := by
    intro region measurable
    constructor
    · have equal : Set.preimage Sum.inl (Set.image (Sum.inr : β → Sum α β) region) =
          Set.empty := by
        apply Set.ext
        intro value
        constructor
        · rintro ⟨input, _, equal⟩
          cases equal
        · exact False.elim
      rw [equal]
      exact left.empty
    · have equal : Set.preimage Sum.inr (Set.image (Sum.inr : β → Sum α β) region) =
          region := by
        apply Set.ext
        intro value
        constructor
        · rintro ⟨input, member, equal⟩
          exact Sum.inr.inj equal ▸ member
        · intro member
          exact ⟨value, member, rfl⟩
      rw [equal]
      exact measurable

@[simp] theorem inl_apply (left : Space α) (right : Space β) (value : α) :
    (inl left right).function value = Sum.inl value := rfl

@[simp] theorem inr_apply (left : Space α) (right : Space β) (value : β) :
    (inr left right).function value = Sum.inr value := rfl

end

end Foundations.Measure.MeasurableEmbedding
