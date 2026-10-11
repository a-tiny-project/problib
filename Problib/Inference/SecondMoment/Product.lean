import Problib.Inference.SecondMoment

set_option autoImplicit false

/-! Independent weighted draws retain both values and multiply their weights.
Their second-moment measure is the product of the two moment measures. The
identity holds at every measurable reading, including infinite integrals.
Only the right law needs an s-finite presentation, as in the construction of
the product measure itself. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v
variable {α : Type u} {β : Type v} {leftSpace : Space α} {rightSpace : Space β}

/-- Retain both independent values and multiply their delivered weights. -/
noncomputable def weightedProductSplit (draws : (α × NNReal) × (β × NNReal)) :
    (α × β) × NNReal :=
  ((draws.1.1, draws.2.1), NNReal.mul draws.1.2 draws.2.2)

theorem weightedProductSplit_measurable (leftSpace : Space α) (rightSpace : Space β) :
    MeasurableMap
      (Space.product (Space.product leftSpace weightSpace) (Space.product rightSpace weightSpace))
      (Space.product (Space.product leftSpace rightSpace) weightSpace) weightedProductSplit := by
  intro set setMeasurable
  have left : MeasurableMap
      (Space.product (Space.product leftSpace weightSpace) (Space.product rightSpace weightSpace))
      (Space.product leftSpace weightSpace) Prod.fst :=
    Space.first_measurable (Space.product leftSpace weightSpace)
    (Space.product rightSpace weightSpace)
  have right : MeasurableMap
      (Space.product (Space.product leftSpace weightSpace) (Space.product rightSpace weightSpace))
      (Space.product rightSpace weightSpace) Prod.snd :=
    Space.second_measurable (Space.product leftSpace weightSpace)
    (Space.product rightSpace weightSpace)
  exact Space.pair_measurable
    (Space.pair_measurable (MeasurableMap.comp (draw_value_measurable leftSpace) left)
      (MeasurableMap.comp (draw_value_measurable rightSpace) right))
    (weight_mul_measurable
      (MeasurableMap.comp (Space.second_measurable leftSpace weightSpace) left)
      (MeasurableMap.comp (Space.second_measurable rightSpace weightSpace) right)) setMeasurable

/-- Squared finite weights preserve s-finiteness, even with infinite total mass. -/
noncomputable def secondMoment_sFinite {space : Space α}
    {weighted : Measure (Space.product space weightSpace)} (finite : Measure.SFinite weighted) :
    Measure.SFinite (secondMoment weighted) := by
  rw [secondMoment_eq_withDensity]
  let source := Space.discrete Unit
  let step := Kernel.const source weighted
  let stepFinite := Kernel.IsSFinite.const source finite
  let density := fun (_ : Unit) (draw : α × NNReal) =>
    ENNReal.finite (NNReal.mul draw.2 draw.2)
  have densityMeasurable : ENNRealMeasurable (Space.product source (Space.product space weightSpace))
      (fun pair => density pair.1 pair.2) :=
    (finite_weight_measurable (weight_mul_measurable (Space.second_measurable space weightSpace)
      (Space.second_measurable space weightSpace))).comp (Space.second_measurable _ _)
  exact ((stepFinite.withDensity density densityMeasurable).measure ()).map
    Prod.fst (draw_value_measurable space)

/-- The moment measure of the split product law is the product of the moment
measures. The left law is arbitrary. No finite-moment or positivity premise is
needed, and the reading used to identify the measures need not separate. -/
theorem secondMoment_weighted_product
    (left : Measure (Space.product leftSpace weightSpace))
    (right : Measure (Space.product rightSpace weightSpace)) (rightFinite : Measure.SFinite right) :
    secondMoment ((Measure.prod left right rightFinite).map weightedProductSplit
      (weightedProductSplit_measurable leftSpace rightSpace)) =
      Measure.prod (secondMoment left) (secondMoment right) (secondMoment_sFinite rightFinite) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have splitMeasurable : MeasurableMap
      (Space.product (Space.product leftSpace weightSpace) (Space.product rightSpace weightSpace))
      (Space.product (Space.product leftSpace rightSpace) weightSpace) weightedProductSplit :=
    weightedProductSplit_measurable leftSpace rightSpace
  have weightedMeasurable : ENNRealMeasurable
      (Space.product (Space.product leftSpace rightSpace) weightSpace)
      (fun draw => ENNReal.mul (ENNReal.mul (drawWeight draw) (drawWeight draw))
        (function draw.1)) := ((drawWeight_measurable (Space.product leftSpace rightSpace)).mul
    (drawWeight_measurable (Space.product leftSpace rightSpace))).mul
      (measurable.comp (draw_value_measurable (Space.product leftSpace rightSpace)))
  have innerMeasurable : ENNRealMeasurable leftSpace
      (fun value => lintegral (secondMoment right) (fun other => function (value, other))) :=
    (Kernel.const leftSpace (secondMoment right)).lintegral_measurable_joint
      (Kernel.IsSFinite.const leftSpace (secondMoment_sFinite rightFinite)) measurable
  rw [lintegral_secondMoment _ measurable,
    lintegral_map _ _ _ weightedMeasurable,
    lintegral_prod _ _ _ (weightedMeasurable.comp splitMeasurable),
    lintegral_prod _ _ _ measurable, lintegral_secondMoment _ innerMeasurable]
  apply lintegral_congr
  intro draw
  have sectionMeasurable : ENNRealMeasurable rightSpace
      (fun other => function (draw.1, other)) :=
    measurable.comp (Kernel.pair_left_measurable draw.1)
  rw [lintegral_secondMoment _ sectionMeasurable,
    ← lintegral_smul right (ENNReal.mul (drawWeight draw) (drawWeight draw))
      (((drawWeight_measurable rightSpace).mul (drawWeight_measurable rightSpace)).mul
        (sectionMeasurable.comp (draw_value_measurable rightSpace)))]
  apply lintegral_congr
  intro other
  change ENNReal.mul
      (ENNReal.mul (ENNReal.finite (NNReal.mul draw.2 other.2))
        (ENNReal.finite (NNReal.mul draw.2 other.2))) (function (draw.1, other.1)) =
    ENNReal.mul (ENNReal.mul (ENNReal.finite draw.2) (ENNReal.finite draw.2))
      (ENNReal.mul (ENNReal.mul (ENNReal.finite other.2) (ENNReal.finite other.2))
        (function (draw.1, other.1)))
  rw [← ENNReal.finite_mul_finite, ENNReal.mul_mul_mul_comm, ENNReal.mul_assoc]

end Problib.Inference
