module

public import Problib.Measure.Space.Sum
public import Problib.Measure.Product

set_option autoImplicit false

namespace Problib.Measure
public section
universe u v w
variable {alpha : Type u} {beta : Type v} {gamma : Type w}

private theorem measurable_congr {carrier : Type u} {space : Space carrier}
    {first second : Set carrier} (measurable : space.Measurable first)
    (same : ∀ value, first value ↔ second value) : space.Measurable second := by
  rw [← Set.ext same]
  exact measurable

private theorem left_product_region (left : Space alpha) (right : Space beta)
    (parameter : Space gamma) {region : Set (alpha × gamma)}
    (measurable : (Space.product left parameter).Measurable region) :
    (Space.product (Space.sum left right) parameter).Measurable
      (fun input => Sum.elim (fun value => region (value, input.2)) (fun _ => False) input.1) := by
  have tag : (Space.product (Space.sum left right) parameter).Measurable
      (fun input => Sum.elim (fun _ => True) (fun _ => False) input.1) :=
    Space.first_measurable _ _ ⟨left.univ, right.empty⟩
  induction measurable with
  | basic member =>
    rcases member with ⟨set, measured, rfl⟩ | ⟨set, measured, rfl⟩
    · exact Space.first_measurable (Space.sum left right) parameter
        (set := Sum.elim set (fun _ => False)) ⟨measured, right.empty⟩
    · have both := (Space.product (Space.sum left right) parameter).inter tag
        (Space.second_measurable _ _ measured)
      apply measurable_congr (space := Space.product (Space.sum left right) parameter) both
      rintro ⟨branch, value⟩
      cases branch <;> simp [Set.inter, Set.preimage, Sum.elim]
  | empty =>
    apply measurable_congr (space := Space.product (Space.sum left right) parameter)
      (Space.product (Space.sum left right) parameter).empty
    rintro ⟨branch, value⟩
    cases branch <;> rfl
  | complement region induction =>
    have both := (Space.product (Space.sum left right) parameter).inter tag
      ((Space.product (Space.sum left right) parameter).complement induction)
    apply measurable_congr (space := Space.product (Space.sum left right) parameter) both
    rintro ⟨branch, value⟩
    cases branch <;> simp [Set.inter, Set.complement, Sum.elim]
  | iUnion regions induction =>
    have union := (Space.product (Space.sum left right) parameter).iUnion induction
    apply measurable_congr (space := Space.product (Space.sum left right) parameter) union
    rintro ⟨branch, value⟩
    cases branch <;> simp [Set.iUnion, Sum.elim]

namespace Space

/-- Distribute a shared parameter into the selected sum branch, measurably. -/
theorem distribute_sum_measurable (left : Space alpha) (right : Space beta)
    (parameter : Space gamma) :
    MeasurableMap (product (sum left right) parameter)
      (sum (product left parameter) (product right parameter))
      (fun input => Sum.elim (fun value => Sum.inl (value, input.2))
        (fun value => Sum.inr (value, input.2)) input.1) := by
  intro region measurable
  have leftRegion := left_product_region left right parameter measurable.1
  have swapped : MeasurableMap (product (sum left right) parameter)
      (product (sum right left) parameter)
      (fun input => (Sum.elim Sum.inr Sum.inl input.1, input.2)) :=
    product_map (MeasurableMap.sum_elim (MeasurableMap.inr right left)
      (MeasurableMap.inl right left)) (MeasurableMap.identity parameter)
  have rightRegion := swapped (left_product_region right left parameter measurable.2)
  have both := (product (sum left right) parameter).union leftRegion rightRegion
  apply measurable_congr (space := product (sum left right) parameter) both
  rintro ⟨branch, value⟩
  cases branch <;> simp [Set.union, Set.preimage, Sum.elim]

end Space
end
end Problib.Measure
