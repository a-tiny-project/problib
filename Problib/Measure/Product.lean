module

public import Problib.Measure.Space

namespace Problib.Measure

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

set_option autoImplicit false

public section

namespace Space

@[expose] def ProductGenerator (left : Space α) (right : Space β) :
    Set (Set (α × β)) :=
  fun set =>
    (∃ leftSet, left.Measurable leftSet ∧
      set = Set.preimage Prod.fst leftSet) ∨
    (∃ rightSet, right.Measurable rightSet ∧
      set = Set.preimage Prod.snd rightSet)

@[expose] def product (left : Space α) (right : Space β) : Space (α × β) :=
  generated (ProductGenerator left right)

@[expose] def Rectangle (left : Space α) (right : Space β) :
    Set (Set (α × β)) :=
  fun set =>
    ∃ leftSet rightSet,
      left.Measurable leftSet ∧ right.Measurable rightSet ∧
        set = Set.product leftSet rightSet

theorem first_measurable (left : Space α) (right : Space β) :
    MeasurableMap (product left right) left Prod.fst := by
  intro set measurable
  exact Generated.basic (Or.inl ⟨set, measurable, rfl⟩)

theorem second_measurable (left : Space α) (right : Space β) :
    MeasurableMap (product left right) right Prod.snd := by
  intro set measurable
  exact Generated.basic (Or.inr ⟨set, measurable, rfl⟩)

theorem product_set_measurable (left : Space α) (right : Space β)
    {leftSet : Set α} {rightSet : Set β}
    (leftMeasurable : left.Measurable leftSet)
    (rightMeasurable : right.Measurable rightSet) :
    (product left right).Measurable (Set.product leftSet rightSet) := by
  exact (product left right).inter
    (first_measurable left right leftMeasurable)
    (second_measurable left right rightMeasurable)

theorem rectangle_measurable {left : Space α} {right : Space β}
    {set : Set (α × β)} (rectangle : Rectangle left right set) :
    (product left right).Measurable set := by
  rcases rectangle with
    ⟨leftSet, rightSet, leftMeasurable, rightMeasurable, rfl⟩
  exact product_set_measurable left right leftMeasurable rightMeasurable

theorem product_eq_generated_rectangles (left : Space α) (right : Space β) :
    product left right = generated (Rectangle left right) := by
  apply Space.ext
  intro set
  constructor
  · apply generated_minimal (generated (Rectangle left right))
    intro generator generatorMember
    cases generatorMember with
    | inl firstGenerator =>
        rcases firstGenerator with ⟨leftSet, leftMeasurable, rfl⟩
        apply Generated.basic
        refine ⟨leftSet, Set.univ, leftMeasurable, right.univ, ?_⟩
        apply Set.ext
        intro value
        exact ⟨fun member => ⟨member, True.intro⟩, fun member => member.1⟩
    | inr secondGenerator =>
        rcases secondGenerator with ⟨rightSet, rightMeasurable, rfl⟩
        apply Generated.basic
        refine ⟨Set.univ, rightSet, left.univ, rightMeasurable, ?_⟩
        apply Set.ext
        intro value
        exact ⟨fun member => ⟨True.intro, member⟩, fun member => member.2⟩
  · exact generated_minimal (product left right) rectangle_measurable

theorem pair_measurable {source : Space α} {left : Space β} {right : Space γ}
    {leftFunction : α → β} {rightFunction : α → γ}
    (leftMeasurable : MeasurableMap source left leftFunction)
    (rightMeasurable : MeasurableMap source right rightFunction) :
    MeasurableMap source (product left right)
      (fun value => (leftFunction value, rightFunction value)) := by
  apply MeasurableMap.into_generated
  intro set generator
  cases generator with
  | inl leftGenerator =>
      rcases leftGenerator with ⟨leftSet, leftSetMeasurable, rfl⟩
      exact leftMeasurable leftSetMeasurable
  | inr rightGenerator =>
      rcases rightGenerator with ⟨rightSet, rightSetMeasurable, rfl⟩
      exact rightMeasurable rightSetMeasurable

theorem pair_measurable_iff {source : Space α} {left : Space β} {right : Space γ}
    {leftFunction : α → β} {rightFunction : α → γ} :
    MeasurableMap source (product left right)
        (fun value => (leftFunction value, rightFunction value)) ↔
      MeasurableMap source left leftFunction ∧
        MeasurableMap source right rightFunction := by
  constructor
  · intro pairMeasurable
    exact ⟨MeasurableMap.comp (first_measurable left right) pairMeasurable,
      MeasurableMap.comp (second_measurable left right) pairMeasurable⟩
  · rintro ⟨leftMeasurable, rightMeasurable⟩
    exact pair_measurable leftMeasurable rightMeasurable

theorem swap_measurable (left : Space α) (right : Space β) :
    MeasurableMap (product left right) (product right left)
      (fun value => (value.2, value.1)) :=
  pair_measurable (second_measurable left right) (first_measurable left right)

theorem associate_measurable (first : Space α) (second : Space β)
    (third : Space γ) :
    MeasurableMap (product (product first second) third)
      (product first (product second third))
      (fun value => (value.1.1, (value.1.2, value.2))) := by
  apply pair_measurable
  · exact MeasurableMap.comp (first_measurable first second)
      (first_measurable (product first second) third)
  · apply pair_measurable
    · exact MeasurableMap.comp (second_measurable first second)
        (first_measurable (product first second) third)
    · exact second_measurable (product first second) third

theorem unassociate_measurable (first : Space α) (second : Space β)
    (third : Space γ) :
    MeasurableMap (product first (product second third))
      (product (product first second) third)
      (fun value => ((value.1, value.2.1), value.2.2)) := by
  apply pair_measurable
  · apply pair_measurable
    · exact first_measurable first (product second third)
    · exact MeasurableMap.comp (first_measurable second third)
        (second_measurable first (product second third))
  · exact MeasurableMap.comp (second_measurable second third)
      (second_measurable first (product second third))

theorem product_map {firstSource : Space α} {secondSource : Space β}
    {firstTarget : Space γ} {secondTarget : Space δ}
    {firstFunction : α → γ} {secondFunction : β → δ}
    (firstMeasurable : MeasurableMap firstSource firstTarget firstFunction)
    (secondMeasurable : MeasurableMap secondSource secondTarget secondFunction) :
    MeasurableMap (product firstSource secondSource)
      (product firstTarget secondTarget)
      (fun value => (firstFunction value.1, secondFunction value.2)) :=
  pair_measurable
    (MeasurableMap.comp firstMeasurable
      (first_measurable firstSource secondSource))
    (MeasurableMap.comp secondMeasurable
      (second_measurable firstSource secondSource))

end Space

end

end Problib.Measure
