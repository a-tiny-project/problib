module
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Measurable.Section
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Measure.Null.Basic
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

/-!
# Pushforwards of product measures

Product measures commute with product maps and reassociate. Pushforwards agree
when their maps agree off a null region.
-/

namespace Problib.Measure
open Problib.Real
public section
universe u v w x

namespace Measure

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

/-- Pushforwards along equal maps are equal, whatever their measurability
certificates. -/
public theorem map_congr_function {source : Space α} {target : Space β}
    (law : Measure source) {first second : α → β}
    (firstMeasurable : MeasurableMap source target first)
    (secondMeasurable : MeasurableMap source target second)
    (equal : first = second) :
    law.map first firstMeasurable = law.map second secondMeasurable := by
  cases equal
  rfl

/-- Pushforwards agree when their maps agree on a measurable region whose
complement is null. -/
public theorem map_congr_on {source : Space α} {target : Space β}
    (law : Measure source) {region : Set α}
    (full : law (Set.complement region) = ENNReal.zero)
    {first second : α → β}
    (firstMeasurable : MeasurableMap source target first)
    (secondMeasurable : MeasurableMap source target second)
    (equal : ∀ value, region value → first value = second value) :
    law.map first firstMeasurable = law.map second secondMeasurable := by
  have restricted : law.restrict region = law :=
    law.restrict_eq_self_of_complement_null full
  apply Measure.ext
  intro set setMeasurable
  rw [law.map_apply first firstMeasurable setMeasurable,
    law.map_apply second secondMeasurable setMeasurable,
    ← restricted,
    law.restrict_apply region (firstMeasurable setMeasurable),
    law.restrict_apply region (secondMeasurable setMeasurable)]
  have sameSet : Set.inter (Set.preimage first set) region =
      Set.inter (Set.preimage second set) region := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨member, inside⟩
      refine ⟨?_, inside⟩
      change set (second value)
      rw [← equal value inside]
      exact member
    · rintro ⟨member, inside⟩
      refine ⟨?_, inside⟩
      change set (first value)
      rw [equal value inside]
      exact member
  rw [sameSet]

/-- Equal right factors give equal products, whatever their s-finite
certificates. -/
public theorem prod_congr_right {first : Space α} {second : Space β}
    (left : Measure first) {before after : Measure second}
    (beforeFinite : SFinite before) (afterFinite : SFinite after)
    (equal : before = after) :
    Measure.prod left before beforeFinite =
      Measure.prod left after afterFinite := by
  cases equal
  exact Measure.prod_certificate_irrelevant left before beforeFinite afterFinite

/-- Pushing a product forward along a product map gives the product of the
pushforwards. -/
public theorem prod_map
    {first : Space α} {second : Space β}
    {firstTarget : Space γ} {secondTarget : Space δ}
    (left : Measure first) (right : Measure second)
    (rightFinite : SFinite right)
    (forwardLeft : α → γ) (forwardRight : β → δ)
    (leftMeasurable : MeasurableMap first firstTarget forwardLeft)
    (rightMeasurable : MeasurableMap second secondTarget forwardRight) :
    (Measure.prod left right rightFinite).map
      (fun pair => (forwardLeft pair.1, forwardRight pair.2))
      (Space.product_map leftMeasurable rightMeasurable) =
    Measure.prod (left.map forwardLeft leftMeasurable)
      (right.map forwardRight rightMeasurable)
      (rightFinite.map forwardRight rightMeasurable) := by
  apply Measure.ext
  intro region regionMeasurable
  rw [Measure.map_apply _ _ _ regionMeasurable,
    Measure.prod_apply left right rightFinite
      (Space.product_map leftMeasurable rightMeasurable regionMeasurable),
    Measure.prod_apply (left.map forwardLeft leftMeasurable)
      (right.map forwardRight rightMeasurable)
      (rightFinite.map forwardRight rightMeasurable) regionMeasurable]
  have sectionMeasurable : ENNRealMeasurable firstTarget
      (fun point => (right.map forwardRight rightMeasurable)
        (Set.preimage (fun value => (point, value)) region)) := by
    exact Kernel.section_apply_measurable
      (Kernel.const firstTarget (right.map forwardRight rightMeasurable))
      (Kernel.IsSFinite.const firstTarget
        (rightFinite.map forwardRight rightMeasurable)) regionMeasurable
  rw [lintegral_map left forwardLeft leftMeasurable sectionMeasurable]
  apply lintegral_congr
  intro point
  change right (Set.preimage forwardRight
      (Set.preimage (fun value => (forwardLeft point, value)) region)) =
    (right.map forwardRight rightMeasurable)
      (Set.preimage (fun value => (forwardLeft point, value)) region)
  exact (Measure.map_apply right forwardRight rightMeasurable
    (Kernel.verticalSection_measurable regionMeasurable (forwardLeft point))).symm

/-- A pushforward in the left factor of a product. -/
public theorem prod_map_left
    {first : Space α} {second : Space β} {firstTarget : Space γ}
    (left : Measure first) (right : Measure second)
    (rightFinite : SFinite right) (forward : α → γ)
    (forwardMeasurable : MeasurableMap first firstTarget forward) :
    Measure.prod (left.map forward forwardMeasurable) right rightFinite =
      (Measure.prod left right rightFinite).map
        (fun pair => (forward pair.1, pair.2))
        (Space.product_map forwardMeasurable (MeasurableMap.identity second)) := by
  rw [prod_map left right rightFinite forward (fun value => value)
    forwardMeasurable (MeasurableMap.identity second)]
  exact (prod_congr_right _ _ _ (Measure.map_id right)).symm

/-- A pushforward in the right factor of a product. -/
public theorem prod_map_right
    {first : Space α} {second : Space β} {secondTarget : Space δ}
    (left : Measure first) (right : Measure second)
    (rightFinite : SFinite right) (forward : β → δ)
    (forwardMeasurable : MeasurableMap second secondTarget forward) :
    Measure.prod left (right.map forward forwardMeasurable)
        (rightFinite.map forward forwardMeasurable) =
      (Measure.prod left right rightFinite).map
        (fun pair => (pair.1, forward pair.2))
        (Space.product_map (MeasurableMap.identity first) forwardMeasurable) := by
  rw [prod_map left right rightFinite (fun value => value) forward
    (MeasurableMap.identity first) forwardMeasurable]
  rw [Measure.map_id left]

/-- Products reassociate: the left-nested product is the right-nested product
regrouped. -/
public theorem prod_associate
    {first : Space α} {second : Space β} {third : Space γ}
    (firstLaw : Measure first) (secondLaw : Measure second)
    (thirdLaw : Measure third)
    (secondFinite : SFinite secondLaw) (thirdFinite : SFinite thirdLaw) :
    Measure.prod (Measure.prod firstLaw secondLaw secondFinite) thirdLaw
        thirdFinite =
      (Measure.prod firstLaw (Measure.prod secondLaw thirdLaw thirdFinite)
          (secondFinite.prod thirdFinite)).map
        (fun value => ((value.1, value.2.1), value.2.2))
        (Space.unassociate_measurable first second third) := by
  apply Measure.ext
  intro region regionMeasurable
  have sectionMeasurable : ENNRealMeasurable (Space.product first second)
      (fun pair => thirdLaw (Set.preimage (fun value => (pair, value)) region)) :=
    Kernel.section_apply_measurable
      (Kernel.const (Space.product first second) thirdLaw)
      (Kernel.IsSFinite.const (Space.product first second) thirdFinite)
      regionMeasurable
  rw [Measure.prod_apply _ thirdLaw thirdFinite regionMeasurable,
    lintegral_prod firstLaw secondLaw secondFinite sectionMeasurable,
    Measure.map_apply _ _ _ regionMeasurable,
    Measure.prod_apply firstLaw _ _
      (Space.unassociate_measurable first second third regionMeasurable)]
  apply lintegral_congr
  intro point
  have sliceMeasurable : (Space.product second third).Measurable
      (Set.preimage (fun value => (point, value))
        (Set.preimage (fun value => ((value.1, value.2.1), value.2.2)) region)) :=
    Kernel.verticalSection_measurable
      (Space.unassociate_measurable first second third regionMeasurable) point
  rw [Measure.prod_apply secondLaw thirdLaw thirdFinite sliceMeasurable]
  rfl

/-- The first marginal of a product is the first factor scaled by the
second factor's total mass. -/
public theorem prod_map_first
    {first : Space α} {second : Space β}
    (left : Measure first) (right : Measure second)
    (rightFinite : SFinite right) :
    (Measure.prod left right rightFinite).map (fun pair => pair.1)
        (Space.first_measurable first second) =
      Measure.smul (right Set.univ) left := by
  apply Measure.ext
  intro set setMeasurable
  have product : Set.preimage (fun pair : α × β => pair.1) set =
      Set.product set Set.univ := by
    apply Set.ext
    intro pair
    exact ⟨fun member => ⟨member, True.intro⟩, fun member => member.1⟩
  rw [Measure.map_apply _ _ _ setMeasurable, product,
    Measure.prod_apply_product left right rightFinite setMeasurable second.univ,
    Measure.smul_apply_measurable _ _ setMeasurable, ENNReal.mul_comm]

/-- Restricting a product to a region of the first coordinate restricts the
first factor. -/
public theorem prod_restrict_left {first : Space α} {second : Space β}
    (left : Measure first) (right : Measure second)
    (rightFinite : SFinite right) {region : Set α}
    (regionMeasurable : first.Measurable region) :
    (Measure.prod left right rightFinite).restrict (fun pair => region pair.1) =
      Measure.prod (left.restrict region) right rightFinite := by
  classical
  have firstRegion : (Space.product first second).Measurable
      (fun pair : α × β => region pair.1) :=
    Space.first_measurable first second regionMeasurable
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.restrict_apply _ _ setMeasurable,
    Measure.prod_apply left right rightFinite
      ((Space.product first second).inter setMeasurable firstRegion),
    Measure.prod_apply (left.restrict region) right rightFinite setMeasurable,
    ← lintegral_indicator left region regionMeasurable]
  apply lintegral_congr
  intro point
  unfold ennrealIndicator ennrealPiecewise
  by_cases member : region point
  · rw [ite_eq_left member]
    have slice : Set.preimage (fun value => (point, value))
        (Set.inter set (fun pair : α × β => region pair.1)) =
        Set.preimage (fun value => (point, value)) set :=
      Set.ext fun _ => ⟨fun inside => inside.1, fun inside => ⟨inside, member⟩⟩
    rw [slice]
  · rw [ite_eq_right member]
    have slice : Set.preimage (fun value => (point, value))
        (Set.inter set (fun pair : α × β => region pair.1)) = Set.empty :=
      Set.ext fun _ => ⟨fun inside => member inside.2, False.elim⟩
    rw [slice, right.empty_apply]

/-- A density on the first factor is a density on the product. -/
public theorem prod_withDensity_left {first : Space α} {second : Space β}
    (left : Measure first) (right : Measure second)
    (rightFinite : SFinite right) {density : α → ENNReal}
    (densityMeasurable : ENNRealMeasurable first density) :
    Measure.prod (left.withDensity density) right rightFinite =
      (Measure.prod left right rightFinite).withDensity
        (fun pair => density pair.1) := by
  apply Measure.ext
  intro set setMeasurable
  have sectionMeasurable : ENNRealMeasurable first
      (fun point => right (Set.preimage (fun value => (point, value)) set)) :=
    Kernel.section_apply_measurable (Kernel.const first right)
      (Kernel.IsSFinite.const first rightFinite) setMeasurable
  have weightMeasurable : ENNRealMeasurable (Space.product first second)
      (fun pair : α × β => density pair.1) :=
    ENNRealMeasurable.comp (map := density) densityMeasurable
      (Space.first_measurable first second)
  rw [Measure.prod_apply _ right rightFinite setMeasurable,
    lintegral_withDensity left densityMeasurable sectionMeasurable,
    Measure.withDensity_apply _ _ setMeasurable,
    ← lintegral_indicator _ set setMeasurable,
    lintegral_prod left right rightFinite
      (ENNRealMeasurable.indicator setMeasurable weightMeasurable)]
  apply lintegral_congr
  intro point
  have sliceMeasurable : second.Measurable
      (Set.preimage (fun value => (point, value)) set) :=
    Kernel.verticalSection_measurable setMeasurable point
  change ENNReal.mul (density point)
      (right (Set.preimage (fun value => (point, value)) set)) =
    lintegral right (ennrealIndicator (Set.preimage (fun value => (point, value)) set)
      (fun _ => density point))
  rw [lintegral_indicator right _ sliceMeasurable, lintegral_const,
    Measure.restrict_apply_univ, ENNReal.mul_comm]

end Measure
end
end Problib.Measure
