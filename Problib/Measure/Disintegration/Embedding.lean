module

public import Problib.Measure.Disintegration.Reconstruction
public import Problib.Measure.Additive.Marginal.Uniqueness
public import Problib.Measure.Kernel.Comap

set_option autoImplicit false

namespace Problib.Measure.Measure.Disintegration

universe u v w

variable {alpha : Type u} {beta : Type v} {gamma : Type w}
  {source : Space alpha} {parameter : Space beta} {ambient : Space gamma}

private theorem comap_reconstruction (joint : Measure (Space.product source parameter))
    (embedding : MeasurableEmbedding source ambient)
    (finite : SigmaFinite (secondMarginal joint))
    (selection : Disintegration (joint.map (fun value => (embedding.function value.1, value.2))
      (Space.product_map embedding.measurable (MeasurableMap.identity parameter)))) :
    reverseSemiproduct (secondMarginal joint) (selection.conditional.comap embedding)
      (selection.conditionalSFinite.comap embedding) = joint := by
  apply ext_of_secondMarginal finite
  intro first second firstMeasurable secondMeasurable _
  rw [reverseSemiproduct_apply_product _ _ _ firstMeasurable secondMeasurable]
  have imageMeasurable := embedding.image_measurable first firstMeasurable
  calc
    _ = lintegral ((secondMarginal joint).restrict second)
        (fun input => selection.conditional input (Set.image embedding.function first)) := by
      apply lintegral_congr
      intro input
      exact Measure.comap_apply (selection.conditional input) embedding firstMeasurable
    _ = joint.map (fun value => (embedding.function value.1, value.2))
        (Space.product_map embedding.measurable (MeasurableMap.identity parameter))
        (Set.product (Set.image embedding.function first) second) := by
      have equal := congrArg (fun measure : Measure (Space.product ambient parameter) =>
        measure (Set.product (Set.image embedding.function first) second)) selection.reconstruction
      rw [reverseSemiproduct_apply_product _ _ _ imageMeasurable secondMeasurable,
        secondMarginal_map_first joint embedding.function embedding.measurable] at equal
      exact equal
    _ = joint (Set.product first second) := by
      rw [Measure.map_apply _ _
        (Space.product_map embedding.measurable (MeasurableMap.identity parameter))
        (Space.product_set_measurable ambient parameter imageMeasurable secondMeasurable)]
      apply congrArg joint
      apply Set.ext
      intro value
      constructor
      · rintro ⟨⟨original, member, equal⟩, secondMember⟩
        exact ⟨embedding.injective equal ▸ member, secondMember⟩
      · intro member
        exact ⟨⟨value.1, member.1, rfl⟩, member.2⟩

/-- Transfer a disintegration of a joint measure mapped along a measurable
embedding of the first coordinate back to the original joint measure under a
sigma-finite second marginal. -/
@[expose] public noncomputable def comap (joint : Measure (Space.product source parameter))
    (embedding : MeasurableEmbedding source ambient)
    (finite : SigmaFinite (secondMarginal joint))
    (selection : Disintegration (joint.map (fun value => (embedding.function value.1, value.2))
      (Space.product_map embedding.measurable (MeasurableMap.identity parameter)))) :
    Disintegration joint where
  conditional := selection.conditional.comap embedding
  conditionalSFinite := selection.conditionalSFinite.comap embedding
  reconstruction := by
    exact comap_reconstruction joint embedding finite selection

end Problib.Measure.Measure.Disintegration
