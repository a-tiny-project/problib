module

public import Foundations.Measure.Equivalence
public import Foundations.Measure.Set.Image

set_option autoImplicit false

namespace Foundations.Measure

universe u v w z

/-- Injective measurable map whose forward image preserves measurable sets. -/
public structure MeasurableEmbedding {α : Type u} {β : Type v}
    (source : Space α) (target : Space β) where
  function : α → β
  injective : Function.Injective function
  measurable : MeasurableMap source target function
  imageMeasurable : ∀ region, source.Measurable region →
    target.Measurable (Set.image function region)

namespace MeasurableEmbedding

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}
  {source : Space α} {middle : Space β} {target : Space γ} {result : Space δ}

@[ext] public theorem ext {left right : MeasurableEmbedding source middle}
    (equal : left.function = right.function) : left = right := by
  cases left
  cases right
  cases equal
  rfl

@[expose] public def identity (space : Space α) : MeasurableEmbedding space space where
  function input := input
  injective := fun _ _ equal => equal
  measurable := MeasurableMap.identity space
  imageMeasurable := by
    intro region measurable
    simpa only [Set.image_id] using measurable

@[expose] public def trans (before : MeasurableEmbedding source middle)
    (after : MeasurableEmbedding middle target) : MeasurableEmbedding source target where
  function input := after.function (before.function input)
  injective := fun _ _ equal => before.injective (after.injective equal)
  measurable := MeasurableMap.comp after.measurable before.measurable
  imageMeasurable := by
    intro region measurable
    rw [Set.image_comp]
    exact after.imageMeasurable _ (before.imageMeasurable region measurable)

@[simp] public theorem identity_trans (embedding : MeasurableEmbedding source middle) :
    (identity source).trans embedding = embedding := by
  apply ext
  rfl

@[simp] public theorem trans_identity (embedding : MeasurableEmbedding source middle) :
    embedding.trans (identity middle) = embedding := by
  apply ext
  rfl

/-- Composition of measurable embeddings is associative. -/
public theorem trans_assoc (first : MeasurableEmbedding source middle)
    (second : MeasurableEmbedding middle target) (third : MeasurableEmbedding target result) :
    (first.trans second).trans third = first.trans (second.trans third) := by
  apply ext
  rfl

/-- The range of a measurable embedding is measurable in the codomain. -/
public theorem range_measurable (embedding : MeasurableEmbedding source middle) :
    middle.Measurable (Set.range embedding.function) := by
  rw [← Set.image_univ]
  exact embedding.imageMeasurable Set.univ source.univ

/-- Construct a measurable embedding from a left inverse with measurable range. -/
@[expose] public def ofLeftInverse (forward : α → β) (inverse : β → α)
    (inverseForward : ∀ value, inverse (forward value) = value)
    (forwardMeasurable : MeasurableMap source middle forward)
    (inverseMeasurable : MeasurableMap middle source inverse)
    (rangeMeasurable : middle.Measurable (Set.range forward)) :
    MeasurableEmbedding source middle where
  function := forward
  injective := fun left right equal =>
    (inverseForward left).symm.trans ((congrArg inverse equal).trans (inverseForward right))
  measurable := forwardMeasurable
  imageMeasurable := by
    intro region measurable
    have equal : Set.image forward region =
        Set.inter (Set.range forward) (Set.preimage inverse region) := by
      apply Set.ext
      intro value
      constructor
      · rintro ⟨input, member, equal⟩
        refine ⟨⟨input, equal⟩, ?_⟩
        change region (inverse value)
        rw [← equal, inverseForward]
        exact member
      · rintro ⟨⟨input, equal⟩, member⟩
        refine ⟨inverse value, member, ?_⟩
        rw [← equal, inverseForward]
    rw [equal]
    exact middle.inter rangeMeasurable (inverseMeasurable measurable)

/-- A measurable embedding restricts to a measurable equivalence onto its range subspace. -/
@[expose] public noncomputable def rangeEquivalence
    (embedding : MeasurableEmbedding source middle) :
    MeasurableEquivalence source
      (Space.comap (fun point : {value : β // Set.range embedding.function value} => point.val)
        middle) := by
  let inverse : {value : β // Set.range embedding.function value} → α :=
    fun point => Classical.choose point.property
  have chosen (point : {value : β // Set.range embedding.function value}) :
      embedding.function (inverse point) = point.val :=
    Classical.choose_spec point.property
  exact {
    forward := fun value => ⟨embedding.function value, value, rfl⟩
    inverse := inverse
    inverse_forward := fun value => embedding.injective (chosen ⟨_, value, rfl⟩)
    forward_inverse := fun point => Subtype.ext (chosen point)
    forward_measurable := by
      intro region measurable
      rcases (Space.comap_measurable_iff _ middle region).mp measurable with
        ⟨targetRegion, targetMeasurable, rfl⟩
      exact embedding.measurable targetMeasurable
    inverse_measurable := by
      intro region measurable
      have equal : Set.preimage inverse region =
          Set.preimage (fun point : {value : β // Set.range embedding.function value} => point.val)
            (Set.image embedding.function region) := by
        apply Set.ext
        intro point
        constructor
        · intro member
          exact ⟨inverse point, member, chosen point⟩
        · rintro ⟨value, member, equal⟩
          have same : value = inverse point :=
            embedding.injective (equal.trans (chosen point).symm)
          change region (inverse point)
          exact same ▸ member
      rw [equal]
      exact Space.comap_map _ middle (embedding.imageMeasurable region measurable)
  }

/-- Canonical inclusion of a measurable subset into the ambient space without
fallback points. -/
@[expose] public def subtype (region : Set α) (regionMeasurable : source.Measurable region) :
    MeasurableEmbedding
      (Space.comap (fun value : {input : α // region input} => value.val) source) source where
  function := fun value => value.val
  injective := fun _ _ equal => Subtype.ext equal
  measurable := Space.comap_map _ source
  imageMeasurable := by
    intro set measurable
    rcases (Space.comap_measurable_iff
      (fun value : {input : α // region input} => value.val) source set).mp measurable with
      ⟨targetSet, targetMeasurable, rfl⟩
    rw [Set.image_subtype_preimage]
    exact source.inter targetMeasurable regionMeasurable

@[simp] public theorem subtype_range (region : Set α)
    (regionMeasurable : source.Measurable region) :
    Set.range (subtype region regionMeasurable).function = region :=
  Set.range_subtype region

end MeasurableEmbedding

namespace MeasurableEquivalence

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

public theorem image_forward (equivalence : MeasurableEquivalence source target)
    (region : Set α) :
    Set.image equivalence.forward region = Set.preimage equivalence.inverse region := by
  apply Set.ext
  intro output
  constructor
  · rintro ⟨input, member, equal⟩
    change region (equivalence.inverse output)
    rw [← equal, equivalence.inverse_forward]
    exact member
  · intro member
    exact ⟨equivalence.inverse output, member, equivalence.forward_inverse output⟩

/-- Canonical measurable embedding induced by a measurable equivalence with
universal range. -/
@[expose] public def toEmbedding (equivalence : MeasurableEquivalence source target) :
    MeasurableEmbedding source target where
  function := equivalence.forward
  injective := equivalence.forward_injective
  measurable := equivalence.forward_measurable
  imageMeasurable := by
    intro region measurable
    rw [equivalence.image_forward]
    exact equivalence.inverse_measurable measurable

@[simp] public theorem toEmbedding_range (equivalence : MeasurableEquivalence source target) :
    Set.range equivalence.toEmbedding.function = Set.univ := by
  apply Set.ext
  intro output
  exact ⟨fun _ => True.intro,
    fun _ => ⟨equivalence.inverse output, equivalence.forward_inverse output⟩⟩

end MeasurableEquivalence

end Foundations.Measure
