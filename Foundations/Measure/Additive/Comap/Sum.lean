module

public import Foundations.Measure.Additive.Comap
public import Foundations.Measure.Embedding.Sum

set_option autoImplicit false

/-!
# Coproduct measure decomposition

Decomposes any measure on a direct sum space into the sum of its pushed-forward
pullbacks along the canonical summand embeddings.
-/
namespace Foundations.Measure.Measure

public section

universe u v

variable {α : Type u} {β : Type v} {left : Space α} {right : Space β}

/-- Decompose any measure on a direct sum space into its pushforward pullback
components along the canonical summand injections. -/
theorem coproduct_decomposition (measure : Measure (Space.sum left right)) :
    Measure.add
      ((measure.comap (MeasurableEmbedding.inl left right)).map
        Sum.inl (MeasurableMap.inl left right))
      ((measure.comap (MeasurableEmbedding.inr left right)).map
        Sum.inr (MeasurableMap.inr left right)) = measure := by
  change Measure.add
    ((measure.comap (MeasurableEmbedding.inl left right)).map
      (MeasurableEmbedding.inl left right).function (MeasurableEmbedding.inl left right).measurable)
    ((measure.comap (MeasurableEmbedding.inr left right)).map
      (MeasurableEmbedding.inr left right).function (MeasurableEmbedding.inr left right).measurable) =
    measure
  rw [map_comap measure (MeasurableEmbedding.inl left right),
    map_comap measure (MeasurableEmbedding.inr left right)]
  have complement : Set.complement (Set.range (Sum.inl : α → Sum α β)) =
      Set.range (Sum.inr : β → Sum α β) := by
    apply Set.ext
    intro input
    cases input with
    | inl value =>
      constructor
      · intro outside
        exact False.elim (outside ⟨value, rfl⟩)
      · rintro ⟨_, equal⟩
        cases equal
    | inr value =>
      constructor
      · intro _
        exact ⟨value, rfl⟩
      · intro _ ⟨_, equal⟩
        cases equal
  change Measure.add (measure.restrict (Set.range Sum.inl))
    (measure.restrict (Set.range Sum.inr)) = measure
  rw [← complement]
  exact measure.restrict_add_complement (MeasurableEmbedding.inl left right).range_measurable

end

end Foundations.Measure.Measure
