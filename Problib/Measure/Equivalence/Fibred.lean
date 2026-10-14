module

public import Problib.Measure.Equivalence.Preserving

set_option autoImplicit false

/-!
# Fibred partial equivalences

A family of partial equivalences indexed by a base point acts fibre by fibre
on the product with the base, and keeps the base point. When each member
changes reference by its own factor, the fibred map changes the product
reference by the factor read at the base point (`reference_change_fibred`).
The proof is Tonelli on both sides and the member's reference change on each
fibre. Acting on the second factor of a product is the constant family
(`productLeft`).
-/

namespace Problib.Measure

open Problib.Real

public section

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  {source : Space α} {target : Space β}

namespace MeasurablePartialEquivalence

/-- Act on each fibre over the base by the member at that base point. The
joint domains and maps must be measurable. -/
@[expose] public def fibred (base : Space ι)
    (family : ι → MeasurablePartialEquivalence source target)
    (sourceMeasurable : (Space.product base source).Measurable
      (fun point => (family point.1).sourceDomain point.2))
    (targetMeasurable : (Space.product base target).Measurable
      (fun point => (family point.1).targetDomain point.2))
    (forwardMeasurable : MeasurableMap (Space.product base source) target
      (fun point => (family point.1).forward point.2))
    (inverseMeasurable : MeasurableMap (Space.product base target) source
      (fun point => (family point.1).inverse point.2)) :
    MeasurablePartialEquivalence (Space.product base source) (Space.product base target) where
  forward := fun point => (point.1, (family point.1).forward point.2)
  inverse := fun point => (point.1, (family point.1).inverse point.2)
  sourceDomain := fun point => (family point.1).sourceDomain point.2
  targetDomain := fun point => (family point.1).targetDomain point.2
  sourceMeasurable := sourceMeasurable
  targetMeasurable := targetMeasurable
  forward_mem := fun point member => (family point.1).forward_mem _ member
  inverse_mem := fun point member => (family point.1).inverse_mem _ member
  inverse_forward := fun point member =>
    Prod.ext rfl ((family point.1).inverse_forward _ member)
  forward_inverse := fun point member =>
    Prod.ext rfl ((family point.1).forward_inverse _ member)
  forwardMeasurable := Space.pair_measurable (Space.first_measurable _ _) forwardMeasurable
  inverseMeasurable := Space.pair_measurable (Space.first_measurable _ _) inverseMeasurable

/-- A fibred map changes the product reference by each member's factor, read
at the base point. -/
public theorem reference_change_fibred (base : Space ι)
    {family : ι → MeasurablePartialEquivalence source target}
    (sourceMeasurable : (Space.product base source).Measurable
      (fun point => (family point.1).sourceDomain point.2))
    (targetMeasurable : (Space.product base target).Measurable
      (fun point => (family point.1).targetDomain point.2))
    (forwardMeasurable : MeasurableMap (Space.product base source) target
      (fun point => (family point.1).forward point.2))
    (inverseMeasurable : MeasurableMap (Space.product base target) source
      (fun point => (family point.1).inverse point.2))
    (baseReference : Measure base)
    {sourceReference : Measure source} {targetReference : Measure target}
    (sourceFinite : Measure.SFinite sourceReference)
    (targetFinite : Measure.SFinite targetReference)
    {factor : ι → β → Real.Carrier}
    (factorMeasurable : MeasurableMap (Space.product base target) Real.borel
      (fun point => factor point.1 point.2))
    (change : ∀ index,
      (family index).ReferenceChange sourceReference targetReference (factor index)) :
    (fibred base family sourceMeasurable targetMeasurable forwardMeasurable
        inverseMeasurable).ReferenceChange
      (Measure.prod baseReference sourceReference sourceFinite)
      (Measure.prod baseReference targetReference targetFinite)
      (fun point => factor point.1 point.2) := by
  unfold ReferenceChange
  change ((Measure.prod baseReference sourceReference sourceFinite).restrict
      (fun point => (family point.1).sourceDomain point.2)).map
      (fun point => (point.1, (family point.1).forward point.2))
      (Space.pair_measurable (Space.first_measurable _ _) forwardMeasurable) =
    ((Measure.prod baseReference targetReference targetFinite).restrict
      (fun point => (family point.1).targetDomain point.2)).withDensity
      (fun point => ENNReal.ofReal (factor point.1 point.2))
  apply Measure.ext_of_lintegral
  intro function functionMeasurable
  have weightMeasurable : ENNRealMeasurable (Space.product base target)
      (fun point => ENNReal.ofReal (factor point.1 point.2)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) Real.ofReal_measurable factorMeasurable
  have movedMeasurable : ENNRealMeasurable (Space.product base source)
      (fun point => function (point.1, (family point.1).forward point.2)) :=
    ENNRealMeasurable.comp functionMeasurable
      (Space.pair_measurable (Space.first_measurable _ _) forwardMeasurable)
  have weightedMeasurable : ENNRealMeasurable (Space.product base target)
      (fun point => ENNReal.mul (ENNReal.ofReal (factor point.1 point.2)) (function point)) :=
    ENNRealMeasurable.mul weightMeasurable functionMeasurable
  rw [lintegral_map _ _ _ functionMeasurable, ← lintegral_indicator _ _ sourceMeasurable,
    lintegral_prod _ _ _ (ENNRealMeasurable.indicator sourceMeasurable movedMeasurable),
    lintegral_withDensity _ weightMeasurable functionMeasurable,
    ← lintegral_indicator _ _ targetMeasurable,
    lintegral_prod _ _ _ (ENNRealMeasurable.indicator targetMeasurable weightedMeasurable)]
  apply lintegral_congr
  intro index
  have slice : MeasurableMap target (Space.product base target) (fun value => (index, value)) :=
    Kernel.pair_left_measurable (source := base) (target := target) index
  have sliceFunction : ENNRealMeasurable target (fun value => function (index, value)) :=
    ENNRealMeasurable.comp functionMeasurable slice
  have sliceWeight : ENNRealMeasurable target
      (fun value => ENNReal.ofReal (factor index value)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) Real.ofReal_measurable
      (MeasurableMap.comp factorMeasurable slice)
  calc
    lintegral sourceReference (fun value =>
        ennrealIndicator (fun point => (family point.1).sourceDomain point.2)
          (fun point => function (point.1, (family point.1).forward point.2))
          (index, value)) =
        lintegral sourceReference (ennrealIndicator (family index).sourceDomain
          (fun value => function (index, (family index).forward value))) := rfl
    _ = lintegral (sourceReference.restrict (family index).sourceDomain)
          (fun value => function (index, (family index).forward value)) :=
        lintegral_indicator _ _ (family index).sourceMeasurable _
    _ = lintegral ((sourceReference.restrict (family index).sourceDomain).map
          (family index).forward (family index).forwardMeasurable)
          (fun value => function (index, value)) :=
        (lintegral_map _ _ _ sliceFunction).symm
    _ = lintegral ((targetReference.restrict (family index).targetDomain).withDensity
          (fun value => ENNReal.ofReal (factor index value)))
          (fun value => function (index, value)) := by
        rw [change index]
    _ = lintegral (targetReference.restrict (family index).targetDomain)
          (fun value => ENNReal.mul (ENNReal.ofReal (factor index value))
            (function (index, value))) :=
        lintegral_withDensity _ sliceWeight sliceFunction
    _ = lintegral targetReference (ennrealIndicator (family index).targetDomain
          (fun value => ENNReal.mul (ENNReal.ofReal (factor index value))
            (function (index, value)))) :=
        (lintegral_indicator _ _ (family index).targetMeasurable _).symm

/-- Act on the second factor and keep the first. -/
@[expose] public def productLeft {δ : Type w} (rest : Space δ)
    (pairing : MeasurablePartialEquivalence source target) :
    MeasurablePartialEquivalence (Space.product rest source) (Space.product rest target) :=
  fibred rest (fun _ => pairing)
    (Space.second_measurable rest source pairing.sourceMeasurable)
    (Space.second_measurable rest target pairing.targetMeasurable)
    (MeasurableMap.comp pairing.forwardMeasurable (Space.second_measurable _ _))
    (MeasurableMap.comp pairing.inverseMeasurable (Space.second_measurable _ _))

/-- A reference change on the second factor carries over, with the first
factor's reference alongside. -/
public theorem reference_change_productLeft {δ : Type w} {rest : Space δ}
    {pairing : MeasurablePartialEquivalence source target}
    {sourceReference : Measure source} {targetReference : Measure target}
    {factor : β → Real.Carrier}
    (restReference : Measure rest) (sourceFinite : Measure.SFinite sourceReference)
    (targetFinite : Measure.SFinite targetReference)
    (factorMeasurable : MeasurableMap target Real.borel factor)
    (change : pairing.ReferenceChange sourceReference targetReference factor) :
    (pairing.productLeft rest).ReferenceChange
      (Measure.prod restReference sourceReference sourceFinite)
      (Measure.prod restReference targetReference targetFinite)
      (fun value => factor value.2) :=
  reference_change_fibred rest
    (Space.second_measurable rest source pairing.sourceMeasurable)
    (Space.second_measurable rest target pairing.targetMeasurable)
    (MeasurableMap.comp pairing.forwardMeasurable (Space.second_measurable _ _))
    (MeasurableMap.comp pairing.inverseMeasurable (Space.second_measurable _ _))
    restReference sourceFinite targetFinite
    (factor := fun _ => factor)
    (MeasurableMap.comp factorMeasurable (Space.second_measurable _ _)) (fun _ => change)

end MeasurablePartialEquivalence

end
end Problib.Measure
