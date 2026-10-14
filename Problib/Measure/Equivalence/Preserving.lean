module

public import Problib.Measure.Equivalence.Partial
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Product.Transport

set_option autoImplicit false

/-!
# Measure-preserving equivalences

A measure-preserving equivalence is a measurable equivalence that pushes one
measure to another. They compose, invert, reassociate and swap products, act
on each factor of a product, and act fibre by fibre when every fibre map
preserves the fibre measure. As partial equivalences with full domains, they
change reference by the constant factor one, so composing one before or after
a partial equivalence keeps its factor (`reference_change_before`,
`reference_change_after`). Factors that agree on the target domain give the
same reference change (`reference_change_congr`).
-/

namespace Problib.Measure

open Problib.Real

public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {first : Space α} {second : Space β} {third : Space γ} {fourth : Space δ}

/-- Two measures agree when they integrate every measurable integrand alike. -/
public theorem Measure.ext_of_lintegral {left right : Measure first}
    (equal : ∀ function, ENNRealMeasurable first function →
      lintegral left function = lintegral right function) :
    left = right := by
  apply Measure.ext
  intro set setMeasurable
  rw [apply_eq_lintegral_indicator _ setMeasurable, apply_eq_lintegral_indicator _ setMeasurable]
  exact equal _ (ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _))

/-- Measurable equivalences act on each factor of a product. -/
@[expose] public def MeasurableEquivalence.product
    (left : MeasurableEquivalence first third) (right : MeasurableEquivalence second fourth) :
    MeasurableEquivalence (Space.product first second) (Space.product third fourth) where
  forward := fun pair => (left.forward pair.1, right.forward pair.2)
  inverse := fun pair => (left.inverse pair.1, right.inverse pair.2)
  inverse_forward := fun pair => by
    change (left.inverse (left.forward pair.1), right.inverse (right.forward pair.2)) = pair
    rw [left.inverse_forward, right.inverse_forward]
  forward_inverse := fun pair => by
    change (left.forward (left.inverse pair.1), right.forward (right.inverse pair.2)) = pair
    rw [left.forward_inverse, right.forward_inverse]
  forward_measurable := Space.product_map left.forward_measurable right.forward_measurable
  inverse_measurable := Space.product_map left.inverse_measurable right.inverse_measurable

/-- Products reassociate. -/
@[expose] public def MeasurableEquivalence.associate (first : Space α) (second : Space β)
    (third : Space γ) :
    MeasurableEquivalence (Space.product (Space.product first second) third)
      (Space.product first (Space.product second third)) where
  forward := fun value => (value.1.1, (value.1.2, value.2))
  inverse := fun value => ((value.1, value.2.1), value.2.2)
  inverse_forward := fun _ => rfl
  forward_inverse := fun _ => rfl
  forward_measurable := Space.associate_measurable first second third
  inverse_measurable := Space.unassociate_measurable first second third

/-- The two factors of a product exchange places. -/
@[expose] public def MeasurableEquivalence.swap (first : Space α) (second : Space β) :
    MeasurableEquivalence (Space.product first second) (Space.product second first) where
  forward := fun value => (value.2, value.1)
  inverse := fun value => (value.2, value.1)
  inverse_forward := fun _ => rfl
  forward_inverse := fun _ => rfl
  forward_measurable := Space.swap_measurable first second
  inverse_measurable := Space.swap_measurable second first

/-- The first factor moves past the second: `(a, (b, c))` goes to `(b, (a, c))`. -/
@[expose] public def MeasurableEquivalence.commuteLeft (first : Space α) (second : Space β)
    (third : Space γ) :
    MeasurableEquivalence (Space.product first (Space.product second third))
      (Space.product second (Space.product first third)) where
  forward := fun value => (value.2.1, (value.1, value.2.2))
  inverse := fun value => (value.2.1, (value.1, value.2.2))
  inverse_forward := fun _ => rfl
  forward_inverse := fun _ => rfl
  forward_measurable := Space.pair_measurable
    (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))
    (Space.pair_measurable (Space.first_measurable _ _)
      (MeasurableMap.comp (Space.second_measurable _ _) (Space.second_measurable _ _)))
  inverse_measurable := Space.pair_measurable
    (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))
    (Space.pair_measurable (Space.first_measurable _ _)
      (MeasurableMap.comp (Space.second_measurable _ _) (Space.second_measurable _ _)))

/-- The second factor moves past the third: `((a, b), c)` goes to `((a, c), b)`. -/
@[expose] public def MeasurableEquivalence.commuteRight (first : Space α) (second : Space β)
    (third : Space γ) :
    MeasurableEquivalence (Space.product (Space.product first second) third)
      (Space.product (Space.product first third) second) where
  forward := fun value => ((value.1.1, value.2), value.1.2)
  inverse := fun value => ((value.1.1, value.2), value.1.2)
  inverse_forward := fun _ => rfl
  forward_inverse := fun _ => rfl
  forward_measurable := Space.pair_measurable
    (Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
      (Space.second_measurable _ _))
    (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))
  inverse_measurable := Space.pair_measurable
    (Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
      (Space.second_measurable _ _))
    (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))

/-- A measurable equivalence that pushes one measure to another. -/
public structure MeasurePreserving (source : Measure first) (target : Measure second) where
  equivalence : MeasurableEquivalence first second
  preserves : source.map equivalence.forward equivalence.forward_measurable = target

namespace MeasurablePartialEquivalence

/-- Factors that agree on the target domain give the same reference change. -/
public theorem reference_change_congr {pairing : MeasurablePartialEquivalence first second}
    {sourceReference : Measure first} {targetReference : Measure second}
    {factor other : β → Real.Carrier}
    (same : ∀ value, pairing.targetDomain value → factor value = other value)
    (change : pairing.ReferenceChange sourceReference targetReference factor) :
    pairing.ReferenceChange sourceReference targetReference other := by
  unfold ReferenceChange at change ⊢
  rw [change]
  apply Measure.withDensity_congr_ae
  exact (targetReference.ae_restrict_mem pairing.targetMeasurable).mono
    (fun value inside => by
      show ENNReal.ofReal (factor value) = ENNReal.ofReal (other value)
      rw [same value inside])

end MeasurablePartialEquivalence

namespace MeasurePreserving

/-- The identity preserves every measure. -/
@[expose] public def refl (measure : Measure first) : MeasurePreserving measure measure where
  equivalence := MeasurableEquivalence.identity first
  preserves := Measure.map_id measure

/-- Measure-preserving equivalences compose. -/
@[expose] public def trans {source : Measure first} {middle : Measure second}
    {target : Measure third}
    (before : MeasurePreserving source middle) (after : MeasurePreserving middle target) :
    MeasurePreserving source target where
  equivalence := before.equivalence.trans after.equivalence
  preserves := by
    change source.map (fun value => after.equivalence.forward (before.equivalence.forward value))
      (MeasurableMap.comp after.equivalence.forward_measurable
        before.equivalence.forward_measurable) = target
    rw [← Measure.map_comp _ _ _ before.equivalence.forward_measurable
      after.equivalence.forward_measurable, before.preserves, after.preserves]

/-- The inverse of a measure-preserving equivalence preserves the measures in
reverse. -/
@[expose] public def symm {source : Measure first} {target : Measure second}
    (preserving : MeasurePreserving source target) : MeasurePreserving target source where
  equivalence := preserving.equivalence.symm
  preserves := by
    change target.map preserving.equivalence.inverse
      preserving.equivalence.inverse_measurable = source
    calc
      target.map preserving.equivalence.inverse preserving.equivalence.inverse_measurable =
          (source.map preserving.equivalence.forward
            preserving.equivalence.forward_measurable).map preserving.equivalence.inverse
            preserving.equivalence.inverse_measurable := by
          rw [preserving.preserves]
      _ = source.map (fun value => value) (MeasurableMap.identity first) := by
          rw [Measure.map_comp _ _ _ preserving.equivalence.forward_measurable
            preserving.equivalence.inverse_measurable]
          exact Measure.map_congr_function _ _ _
            (funext preserving.equivalence.inverse_forward)
      _ = source := Measure.map_id source

/-- A measurable equivalence that agrees with a preserving one preserves the
same measures. -/
@[expose] public def congr {source : Measure first} {target : Measure second}
    (preserving : MeasurePreserving source target)
    (equivalence : MeasurableEquivalence first second)
    (same : ∀ value, equivalence.forward value = preserving.equivalence.forward value) :
    MeasurePreserving source target where
  equivalence := equivalence
  preserves := by
    rw [Measure.map_congr_function _ _ preserving.equivalence.forward_measurable
      (funext same)]
    exact preserving.preserves

/-- Products reassociate. -/
@[expose] public def associate (firstLaw : Measure first) (secondLaw : Measure second)
    (thirdLaw : Measure third) (secondFinite : Measure.SFinite secondLaw)
    (thirdFinite : Measure.SFinite thirdLaw) :
    MeasurePreserving
      (Measure.prod (Measure.prod firstLaw secondLaw secondFinite) thirdLaw thirdFinite)
      (Measure.prod firstLaw (Measure.prod secondLaw thirdLaw thirdFinite)
        (secondFinite.prod thirdFinite)) where
  equivalence := MeasurableEquivalence.associate first second third
  preserves := by
    change (Measure.prod (Measure.prod firstLaw secondLaw secondFinite) thirdLaw
        thirdFinite).map (fun value => (value.1.1, (value.1.2, value.2)))
        (Space.associate_measurable first second third) = _
    rw [Measure.prod_associate firstLaw secondLaw thirdLaw secondFinite thirdFinite,
      Measure.map_comp _ _ _ (Space.unassociate_measurable first second third)
        (Space.associate_measurable first second third)]
    exact Measure.map_id _

/-- Products swap their factors. -/
@[expose] public def swap (left : Measure first) (right : Measure second)
    (leftFinite : Measure.SFinite left) (rightFinite : Measure.SFinite right) :
    MeasurePreserving (Measure.prod left right rightFinite) (Measure.prod right left leftFinite)
    where
  equivalence := MeasurableEquivalence.swap first second
  preserves := Measure.prod_swap leftFinite rightFinite

/-- Preserving equivalences act on each factor of a product. -/
@[expose] public def product {left : Measure first} {leftImage : Measure third}
    {right : Measure second} {rightImage : Measure fourth}
    (rightFinite : Measure.SFinite right) (rightImageFinite : Measure.SFinite rightImage)
    (onLeft : MeasurePreserving left leftImage) (onRight : MeasurePreserving right rightImage) :
    MeasurePreserving (Measure.prod left right rightFinite)
      (Measure.prod leftImage rightImage rightImageFinite) where
  equivalence := onLeft.equivalence.product onRight.equivalence
  preserves := by
    change (Measure.prod left right rightFinite).map
      (fun pair => (onLeft.equivalence.forward pair.1, onRight.equivalence.forward pair.2))
      (Space.product_map onLeft.equivalence.forward_measurable
        onRight.equivalence.forward_measurable) = _
    rw [Measure.prod_map left right rightFinite _ _ onLeft.equivalence.forward_measurable
      onRight.equivalence.forward_measurable, onLeft.preserves]
    exact Measure.prod_congr_right _ _ _ onRight.preserves

/-- The first factor of a product moves past the second. -/
@[expose] public noncomputable def commuteLeft (firstLaw : Measure first)
    (secondLaw : Measure second) (thirdLaw : Measure third) (firstFinite : Measure.SFinite firstLaw)
    (secondFinite : Measure.SFinite secondLaw) (thirdFinite : Measure.SFinite thirdLaw) :
    MeasurePreserving
      (Measure.prod firstLaw (Measure.prod secondLaw thirdLaw thirdFinite)
        (secondFinite.prod thirdFinite))
      (Measure.prod secondLaw (Measure.prod firstLaw thirdLaw thirdFinite)
        (firstFinite.prod thirdFinite)) :=
  ((associate firstLaw secondLaw thirdLaw secondFinite thirdFinite).symm.trans
    ((product thirdFinite thirdFinite (swap firstLaw secondLaw firstFinite secondFinite)
      (refl thirdLaw)).trans
      (associate secondLaw firstLaw thirdLaw firstFinite thirdFinite))).congr
    (MeasurableEquivalence.commuteLeft first second third) (fun _ => rfl)

/-- The second factor of a product moves past the third. -/
@[expose] public noncomputable def commuteRight (firstLaw : Measure first)
    (secondLaw : Measure second) (thirdLaw : Measure third)
    (secondFinite : Measure.SFinite secondLaw) (thirdFinite : Measure.SFinite thirdLaw) :
    MeasurePreserving
      (Measure.prod (Measure.prod firstLaw secondLaw secondFinite) thirdLaw thirdFinite)
      (Measure.prod (Measure.prod firstLaw thirdLaw thirdFinite) secondLaw secondFinite) :=
  ((associate firstLaw secondLaw thirdLaw secondFinite thirdFinite).trans
    ((product (secondFinite.prod thirdFinite) (thirdFinite.prod secondFinite)
      (refl firstLaw) (swap secondLaw thirdLaw secondFinite thirdFinite)).trans
      (associate firstLaw thirdLaw secondLaw thirdFinite secondFinite).symm)).congr
    (MeasurableEquivalence.commuteRight first second third) (fun _ => rfl)

/-- A preserving equivalence carries its measures along equalities. -/
@[expose] public def cast {source source' : Measure first} {target target' : Measure second}
    (preserving : MeasurePreserving source target) (sameSource : source = source')
    (sameTarget : target = target') : MeasurePreserving source' target' where
  equivalence := preserving.equivalence
  preserves := by
    rw [← sameSource, ← sameTarget]
    exact preserving.preserves

/-- Products regroup their inner factors: `((a, b), (c, d))` goes to
`((a, c), (b, d))`. -/
@[expose] public noncomputable def interchange
    {ε : Type u} {ζ : Type v} {η : Type w} {θ : Type x}
    {firstSpace : Space ε} {secondSpace : Space ζ} {thirdSpace : Space η}
    {fourthSpace : Space θ}
    (firstLaw : Measure firstSpace) (secondLaw : Measure secondSpace)
    (thirdLaw : Measure thirdSpace) (fourthLaw : Measure fourthSpace)
    (secondFinite : Measure.SFinite secondLaw) (thirdFinite : Measure.SFinite thirdLaw)
    (fourthFinite : Measure.SFinite fourthLaw) :
    MeasurePreserving
      (Measure.prod (Measure.prod firstLaw secondLaw secondFinite)
        (Measure.prod thirdLaw fourthLaw fourthFinite) (thirdFinite.prod fourthFinite))
      (Measure.prod (Measure.prod firstLaw thirdLaw thirdFinite)
        (Measure.prod secondLaw fourthLaw fourthFinite) (secondFinite.prod fourthFinite)) :=
  let regroupInner :=
    (associate secondLaw thirdLaw fourthLaw thirdFinite fourthFinite).symm
  let swapInner := product fourthFinite fourthFinite
    (swap secondLaw thirdLaw secondFinite thirdFinite) (refl fourthLaw)
  let reassociateInner := associate thirdLaw secondLaw fourthLaw secondFinite fourthFinite
  (((((associate firstLaw secondLaw (Measure.prod thirdLaw fourthLaw fourthFinite)
      secondFinite (thirdFinite.prod fourthFinite)).trans
    (product (secondFinite.prod (thirdFinite.prod fourthFinite))
      ((secondFinite.prod thirdFinite).prod fourthFinite) (refl firstLaw) regroupInner)).trans
    (product ((secondFinite.prod thirdFinite).prod fourthFinite)
      ((thirdFinite.prod secondFinite).prod fourthFinite) (refl firstLaw) swapInner)).trans
    (product ((thirdFinite.prod secondFinite).prod fourthFinite)
      (thirdFinite.prod (secondFinite.prod fourthFinite)) (refl firstLaw)
      reassociateInner)).trans
    (associate firstLaw thirdLaw (Measure.prod secondLaw fourthLaw fourthFinite)
      thirdFinite (secondFinite.prod fourthFinite)).symm)

/-- A product is preserved by maps that act on each fibre over the first
factor, when each fibre map preserves the second factor. -/
@[expose] public def fibre (left : Measure first) (right : Measure second)
    (rightFinite : Measure.SFinite right) (forward inverse : α → β → β)
    (forwardMeasurable : MeasurableMap (Space.product first second) second
      (fun pair => forward pair.1 pair.2))
    (inverseMeasurable : MeasurableMap (Space.product first second) second
      (fun pair => inverse pair.1 pair.2))
    (inverse_forward : ∀ base value, inverse base (forward base value) = value)
    (forward_inverse : ∀ base value, forward base (inverse base value) = value)
    (fibres : ∀ base, right.map (forward base)
      (MeasurableMap.comp forwardMeasurable
        (Kernel.pair_left_measurable (source := first) (target := second) base)) = right) :
    MeasurePreserving (Measure.prod left right rightFinite) (Measure.prod left right rightFinite)
    where
  equivalence :=
    { forward := fun pair => (pair.1, forward pair.1 pair.2)
      inverse := fun pair => (pair.1, inverse pair.1 pair.2)
      inverse_forward := fun pair => by
        change (pair.1, inverse pair.1 (forward pair.1 pair.2)) = pair
        rw [inverse_forward]
      forward_inverse := fun pair => by
        change (pair.1, forward pair.1 (inverse pair.1 pair.2)) = pair
        rw [forward_inverse]
      forward_measurable := Space.pair_measurable (Space.first_measurable _ _) forwardMeasurable
      inverse_measurable := Space.pair_measurable (Space.first_measurable _ _) inverseMeasurable }
  preserves := by
    apply Measure.ext_of_lintegral
    intro function functionMeasurable
    have moved : ENNRealMeasurable (Space.product first second)
        (fun pair => function (pair.1, forward pair.1 pair.2)) :=
      ENNRealMeasurable.comp functionMeasurable
        (Space.pair_measurable (Space.first_measurable _ _) forwardMeasurable)
    change lintegral ((Measure.prod left right rightFinite).map
      (fun pair => (pair.1, forward pair.1 pair.2))
      (Space.pair_measurable (Space.first_measurable _ _) forwardMeasurable)) function = _
    rw [lintegral_map _ _ _ functionMeasurable, lintegral_prod _ _ _ moved,
      lintegral_prod _ _ _ functionMeasurable]
    apply lintegral_congr
    intro base
    have sectionMeasurable : ENNRealMeasurable second (fun value => function (base, value)) :=
      ENNRealMeasurable.comp functionMeasurable
        (Kernel.pair_left_measurable (source := first) (target := second) base)
    rw [← lintegral_map right (forward base)
      (MeasurableMap.comp forwardMeasurable
        (Kernel.pair_left_measurable (source := first) (target := second) base))
      sectionMeasurable, fibres base]

/-- As a partial equivalence with full domains, a measure-preserving
equivalence changes reference by one. -/
public theorem reference_change {source : Measure first} {target : Measure second}
    (preserving : MeasurePreserving source target) :
    (MeasurablePartialEquivalence.ofEquivalence preserving.equivalence).ReferenceChange
      source target (fun _ => Construction.Dedekind.one) := by
  unfold MeasurablePartialEquivalence.ReferenceChange
  change (source.restrict Set.univ).map preserving.equivalence.forward
      preserving.equivalence.forward_measurable =
    (target.restrict Set.univ).withDensity (fun _ => ENNReal.ofReal Construction.Dedekind.one)
  have unit : (fun _ : β => ENNReal.ofReal Construction.Dedekind.one) =
      (fun _ => ENNReal.one) := funext fun _ => ENNReal.ofReal_one
  rw [Measure.restrict_univ, Measure.restrict_univ, unit, Measure.withDensity_one,
    preserving.preserves]

/-- A preserving equivalence before a partial equivalence keeps its factor. -/
public theorem reference_change_before {source : Measure first} {target : Measure second}
    (preserving : MeasurePreserving source target)
    {after : MeasurablePartialEquivalence second third} {thirdReference : Measure third}
    {factor : γ → Real.Carrier} (factorMeasurable : MeasurableMap third Real.borel factor)
    (change : after.ReferenceChange target thirdReference factor)
    (nonnegative : ∀ value, after.targetDomain value →
      Construction.Dedekind.le Construction.Dedekind.zero (factor value)) :
    ((MeasurablePartialEquivalence.ofEquivalence preserving.equivalence).trans
      after).ReferenceChange source thirdReference factor := by
  have composite := MeasurablePartialEquivalence.reference_change_trans
    (MeasurableMap.constant second Real.borel Construction.Dedekind.one) factorMeasurable
    preserving.reference_change change
    (fun _ _ => Construction.Dedekind.le_of_lt Construction.Dedekind.one_positive) nonnegative
  refine MeasurablePartialEquivalence.reference_change_congr (fun value _ => ?_) composite
  exact Construction.Dedekind.mul_one _

/-- A preserving equivalence after a partial equivalence reads its factor
through the inverse. -/
public theorem reference_change_after {sourceReference : Measure first}
    {middle : Measure second} {target : Measure third}
    {before : MeasurablePartialEquivalence first second}
    (preserving : MeasurePreserving middle target)
    {factor : β → Real.Carrier} (factorMeasurable : MeasurableMap second Real.borel factor)
    (change : before.ReferenceChange sourceReference middle factor)
    (nonnegative : ∀ value, before.targetDomain value →
      Construction.Dedekind.le Construction.Dedekind.zero (factor value)) :
    (before.trans (MeasurablePartialEquivalence.ofEquivalence
      preserving.equivalence)).ReferenceChange sourceReference target
      (fun value => factor (preserving.equivalence.inverse value)) := by
  have composite := MeasurablePartialEquivalence.reference_change_trans factorMeasurable
    (MeasurableMap.constant third Real.borel Construction.Dedekind.one) change
    preserving.reference_change nonnegative
    (fun _ _ => Construction.Dedekind.le_of_lt Construction.Dedekind.one_positive)
  refine MeasurablePartialEquivalence.reference_change_congr (fun value _ => ?_) composite
  exact Construction.Dedekind.one_mul _

end MeasurePreserving

end
end Problib.Measure
