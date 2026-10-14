module

public import Problib.Measure.Embedding.Basic
public import Problib.Measure.Product

set_option autoImplicit false

namespace Problib.Measure.MeasurableEmbedding

universe u v w z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}
  {firstSource : Space α} {secondSource : Space β}
  {firstTarget : Space γ} {secondTarget : Space δ}

/-- Product of two measurable embeddings, preserving measurable rectangles and sets. -/
@[expose] public def product (first : MeasurableEmbedding firstSource firstTarget)
    (second : MeasurableEmbedding secondSource secondTarget) :
    MeasurableEmbedding (Space.product firstSource secondSource)
      (Space.product firstTarget secondTarget) := by
  let function : α × β → γ × δ :=
    fun value => (first.function value.1, second.function value.2)
  have injective : Function.Injective function := by
    intro left right equal
    exact Prod.ext (first.injective (congrArg Prod.fst equal))
      (second.injective (congrArg Prod.snd equal))
  have imageRectangle (left : Set α) (right : Set β) :
      Set.image function (Set.product left right) =
        Set.product (Set.image first.function left) (Set.image second.function right) := by
    apply Set.ext
    intro point
    constructor
    · rintro ⟨value, member, equal⟩
      exact ⟨⟨value.1, member.1, congrArg Prod.fst equal⟩,
        ⟨value.2, member.2, congrArg Prod.snd equal⟩⟩
    · rintro ⟨⟨leftValue, leftMember, leftEqual⟩,
        ⟨rightValue, rightMember, rightEqual⟩⟩
      exact ⟨(leftValue, rightValue), ⟨leftMember, rightMember⟩,
        Prod.ext leftEqual rightEqual⟩
  have rangeEqual : Set.range function =
      Set.product (Set.range first.function) (Set.range second.function) := by
    have univEqual : (Set.univ : Set (α × β)) = Set.product Set.univ Set.univ := by
      apply Set.ext
      intro point
      exact ⟨fun _ => ⟨True.intro, True.intro⟩, fun _ => True.intro⟩
    rw [← Set.image_univ function, univEqual, imageRectangle,
      Set.image_univ, Set.image_univ]
  have rangeMeasurable :
      (Space.product firstTarget secondTarget).Measurable (Set.range function) := by
    rw [rangeEqual]
    exact Space.product_set_measurable firstTarget secondTarget
      first.range_measurable second.range_measurable
  exact {
    function := function
    injective := injective
    measurable := Space.product_map first.measurable second.measurable
    image_measurable := by
      intro region measurable
      rw [Space.product_eq_generated_rectangles] at measurable
      induction measurable with
      | basic rectangle =>
          rcases rectangle with ⟨left, right, leftMeasurable, rightMeasurable, rfl⟩
          rw [imageRectangle]
          exact Space.product_set_measurable firstTarget secondTarget
            (first.image_measurable left leftMeasurable)
            (second.image_measurable right rightMeasurable)
      | empty =>
          rw [Set.image_empty]
          exact (Space.product firstTarget secondTarget).empty
      | @complement region _ induction =>
          have equal : Set.image function (Set.complement region) =
              Set.difference (Set.range function) (Set.image function region) := by
            apply Set.ext
            intro point
            constructor
            · rintro ⟨value, missing, equal⟩
              refine ⟨⟨value, equal⟩, ?_⟩
              rintro ⟨other, member, otherEqual⟩
              exact missing (injective (otherEqual.trans equal.symm) ▸ member)
            · rintro ⟨⟨value, equal⟩, missing⟩
              exact ⟨value, fun member => missing ⟨value, member, equal⟩, equal⟩
          rw [equal]
          exact (Space.product firstTarget secondTarget).difference rangeMeasurable induction
      | iUnion _ induction =>
          rw [Set.image_iUnion]
          exact (Space.product firstTarget secondTarget).iUnion induction
  }

/-- The range of a product embedding is the Cartesian product of the individual ranges. -/
public theorem product_range (first : MeasurableEmbedding firstSource firstTarget)
    (second : MeasurableEmbedding secondSource secondTarget) :
    Set.range (first.product second).function =
      Set.product (Set.range first.function) (Set.range second.function) := by
  apply Set.ext
  intro point
  constructor
  · rintro ⟨value, equal⟩
    exact ⟨⟨value.1, congrArg Prod.fst equal⟩, ⟨value.2, congrArg Prod.snd equal⟩⟩
  · rintro ⟨⟨left, leftEqual⟩, ⟨right, rightEqual⟩⟩
    exact ⟨(left, right), Prod.ext leftEqual rightEqual⟩

end Problib.Measure.MeasurableEmbedding
