module
public import Problib.Measure.Equivalence
public import Problib.Measure.Product
public import Problib.Measure.Real.Interval
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.AlmostEverywhere.Transport
public import Problib.Measure.Kernel.Product.Transport
public import Problib.Measure.Real.Arithmetic
import Problib.Measure.Measurability.Real

set_option autoImplicit false
namespace Problib.Measure
open Problib.Real Measure
open Problib.Real
public section
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
  {source : Space α} {target : Space β} {third : Space γ}

/-- Global measurable maps inverse on stated measurable domains. -/
public structure MeasurablePartialEquivalence (source : Space α) (target : Space β) where
  forward : α → β
  inverse : β → α
  sourceDomain : Set α
  targetDomain : Set β
  sourceMeasurable : source.Measurable sourceDomain
  targetMeasurable : target.Measurable targetDomain
  forward_mem : ∀ value, sourceDomain value → targetDomain (forward value)
  inverse_mem : ∀ value, targetDomain value → sourceDomain (inverse value)
  inverse_forward : ∀ value, sourceDomain value → inverse (forward value) = value
  forward_inverse : ∀ value, targetDomain value → forward (inverse value) = value
  forwardMeasurable : MeasurableMap source target forward
  inverseMeasurable : MeasurableMap target source inverse

namespace MeasurablePartialEquivalence
@[expose] public def symm (pairing : MeasurablePartialEquivalence source target) :
    MeasurablePartialEquivalence target source where
  forward := pairing.inverse
  inverse := pairing.forward
  sourceDomain := pairing.targetDomain
  targetDomain := pairing.sourceDomain
  sourceMeasurable := pairing.targetMeasurable
  targetMeasurable := pairing.sourceMeasurable
  forward_mem := pairing.inverse_mem
  inverse_mem := pairing.forward_mem
  inverse_forward := pairing.forward_inverse
  forward_inverse := pairing.inverse_forward
  forwardMeasurable := pairing.inverseMeasurable
  inverseMeasurable := pairing.forwardMeasurable

/-- Change of reference is a density at the forward image. -/
@[expose] public def ReferenceChange (pairing : MeasurablePartialEquivalence source target)
    (sourceReference : Measure source) (targetReference : Measure target)
    (factor : β → Real.Carrier) : Prop :=
  (sourceReference.restrict pairing.sourceDomain).map pairing.forward pairing.forwardMeasurable =
    (targetReference.restrict pairing.targetDomain).withDensity
      (fun value => ENNReal.ofReal (factor value))

/-- A measurable equivalence is a partial equivalence with full domains. -/
@[expose] public def ofEquivalence (equivalence : MeasurableEquivalence source target) :
    MeasurablePartialEquivalence source target where
  forward := equivalence.forward
  inverse := equivalence.inverse
  sourceDomain := Set.univ
  targetDomain := Set.univ
  sourceMeasurable := source.univ
  targetMeasurable := target.univ
  forward_mem := fun _ _ => True.intro
  inverse_mem := fun _ _ => True.intro
  inverse_forward := fun value _ => equivalence.inverse_forward value
  forward_inverse := fun value _ => equivalence.forward_inverse value
  forwardMeasurable := equivalence.forward_measurable
  inverseMeasurable := equivalence.inverse_measurable

@[expose] public def trans
    (before : MeasurablePartialEquivalence source target)
    (after : MeasurablePartialEquivalence target third) :
    MeasurablePartialEquivalence source third where
  forward := fun value => after.forward (before.forward value)
  inverse := fun value => before.inverse (after.inverse value)
  sourceDomain := fun value =>
    before.sourceDomain value ∧ after.sourceDomain (before.forward value)
  targetDomain := fun value =>
    after.targetDomain value ∧ before.targetDomain (after.inverse value)
  sourceMeasurable := source.inter before.sourceMeasurable
    (before.forwardMeasurable after.sourceMeasurable)
  targetMeasurable := third.inter after.targetMeasurable
    (after.inverseMeasurable before.targetMeasurable)
  forward_mem := by
    intro value member
    exact ⟨after.forward_mem _ member.2,
      by rw [after.inverse_forward _ member.2]; exact before.forward_mem _ member.1⟩
  inverse_mem := by
    intro value member
    exact ⟨before.inverse_mem _ member.2,
      by rw [before.forward_inverse _ member.2]; exact after.inverse_mem _ member.1⟩
  inverse_forward := by
    intro value member
    rw [after.inverse_forward _ member.2, before.inverse_forward _ member.1]
  forward_inverse := by
    intro value member
    rw [before.forward_inverse _ member.2, after.forward_inverse _ member.1]
  forwardMeasurable := MeasurableMap.comp after.forwardMeasurable before.forwardMeasurable
  inverseMeasurable := MeasurableMap.comp before.inverseMeasurable after.inverseMeasurable

@[expose] public def productRight {δ : Type w} (rest : Space δ)
    (pairing : MeasurablePartialEquivalence source target) :
    MeasurablePartialEquivalence
      (Space.product source rest) (Space.product target rest) where
  forward := fun input => (pairing.forward input.1, input.2)
  inverse := fun input => (pairing.inverse input.1, input.2)
  sourceDomain := fun input => pairing.sourceDomain input.1
  targetDomain := fun input => pairing.targetDomain input.1
  sourceMeasurable := Space.first_measurable source rest pairing.sourceMeasurable
  targetMeasurable := Space.first_measurable target rest pairing.targetMeasurable
  forward_mem := fun _ member => pairing.forward_mem _ member
  inverse_mem := fun _ member => pairing.inverse_mem _ member
  inverse_forward := by
    intro input member
    apply Prod.ext
    · exact pairing.inverse_forward _ member
    · rfl
  forward_inverse := by
    intro input member
    apply Prod.ext
    · exact pairing.forward_inverse _ member
    · rfl
  forwardMeasurable := Space.product_map pairing.forwardMeasurable
    (MeasurableMap.identity rest)
  inverseMeasurable := Space.product_map pairing.inverseMeasurable
    (MeasurableMap.identity rest)

/-- Undoing a reference change reweights by the reciprocal factor, read at
the forward image. -/
public theorem reference_change_symm
    {pairing : MeasurablePartialEquivalence source target}
    {sourceReference : Measure source} {targetReference : Measure target}
    {factor : β → Real.Carrier}
    (factorMeasurable : MeasurableMap target Real.borel factor)
    (change : pairing.ReferenceChange sourceReference targetReference factor)
    (positive : ∀ value, pairing.targetDomain value →
      Construction.Dedekind.lt Construction.Dedekind.zero (factor value)) :
    pairing.symm.ReferenceChange targetReference sourceReference
      (fun value => Construction.Dedekind.inverse (factor (pairing.forward value))) := by
  have weightMeasurable : ENNRealMeasurable target
      (fun value => ENNReal.ofReal (factor value)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) Real.ofReal_measurable
      factorMeasurable
  have reciprocalMeasurable : ENNRealMeasurable source
      (fun value => ENNReal.ofReal
        (Construction.Dedekind.inverse (factor (pairing.forward value)))) := by
    measurability [pairing.forwardMeasurable]
  have returned : sourceReference.restrict pairing.sourceDomain =
      ((targetReference.restrict pairing.targetDomain).withDensity
        (fun value => ENNReal.ofReal (factor value))).map pairing.inverse
        pairing.inverseMeasurable := by
    unfold ReferenceChange at change
    rw [← change, Measure.map_comp,
      Measure.map_congr_on _
        (Measure.ae_restrict_mem sourceReference pairing.sourceMeasurable) _
        (MeasurableMap.identity source) pairing.inverse_forward,
      Measure.map_id]
  unfold ReferenceChange
  change (targetReference.restrict pairing.targetDomain).map pairing.inverse
      pairing.inverseMeasurable =
    (sourceReference.restrict pairing.sourceDomain).withDensity
      (fun value => ENNReal.ofReal
        (Construction.Dedekind.inverse (factor (pairing.forward value))))
  rw [returned, ← Measure.map_withDensity _ pairing.inverse pairing.inverseMeasurable
      reciprocalMeasurable,
    Measure.withDensity_withDensity _ weightMeasurable
      (ENNRealMeasurable.comp
        (map := fun value => ENNReal.ofReal
          (Construction.Dedekind.inverse (factor (pairing.forward value))))
        reciprocalMeasurable pairing.inverseMeasurable)]
  have cancel : (targetReference.restrict pairing.targetDomain).AEEq
      (fun value => ENNReal.mul (ENNReal.ofReal (factor value))
        (ENNReal.ofReal (Construction.Dedekind.inverse
          (factor (pairing.forward (pairing.inverse value))))))
      (fun _ => ENNReal.one) := by
    apply (Measure.ae_restrict_mem targetReference pairing.targetMeasurable).mono
    intro value inside
    change ENNReal.mul _ _ = ENNReal.one
    rw [pairing.forward_inverse value inside]
    exact Real.ofReal_mul_ofReal_inverse (positive value inside)
  rw [Measure.withDensity_congr_ae cancel, Measure.withDensity_one]

/-- Reference changes compose: the factors multiply, the first read back
through the second pairing's inverse. -/
public theorem reference_change_trans
    {before : MeasurablePartialEquivalence source target}
    {after : MeasurablePartialEquivalence target third}
    {sourceReference : Measure source} {targetReference : Measure target}
    {thirdReference : Measure third}
    {beforeFactor : β → Real.Carrier} {afterFactor : γ → Real.Carrier}
    (beforeMeasurable : MeasurableMap target Real.borel beforeFactor)
    (afterMeasurable : MeasurableMap third Real.borel afterFactor)
    (beforeChange :
      before.ReferenceChange sourceReference targetReference beforeFactor)
    (afterChange :
      after.ReferenceChange targetReference thirdReference afterFactor)
    (beforeNonnegative : ∀ value, before.targetDomain value →
      Construction.Dedekind.le Construction.Dedekind.zero (beforeFactor value))
    (afterNonnegative : ∀ value, after.targetDomain value →
      Construction.Dedekind.le Construction.Dedekind.zero (afterFactor value)) :
    (before.trans after).ReferenceChange sourceReference thirdReference
      (fun value => Construction.Dedekind.mul (afterFactor value)
        (beforeFactor (after.inverse value))) := by
  classical
  have beforeWeight : ENNRealMeasurable target
      (fun value => ENNReal.ofReal (beforeFactor value)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) Real.ofReal_measurable
      beforeMeasurable
  have afterWeight : ENNRealMeasurable third
      (fun value => ENNReal.ofReal (afterFactor value)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) Real.ofReal_measurable
      afterMeasurable
  have returnedMeasurable : third.Measurable
      (Set.preimage after.inverse before.targetDomain) :=
    after.inverseMeasurable before.targetMeasurable
  let returnedWeight : γ → ENNReal := ennrealIndicator
    (Set.preimage after.inverse before.targetDomain)
    (fun value => ENNReal.ofReal (beforeFactor (after.inverse value)))
  have returnedWeightMeasurable : ENNRealMeasurable third returnedWeight :=
    ENNRealMeasurable.indicator returnedMeasurable
      (ENNRealMeasurable.comp
        (map := fun value => ENNReal.ofReal (beforeFactor value))
        beforeWeight after.inverseMeasurable)
  have sameSource : (before.trans after).sourceDomain =
      Set.inter (Set.preimage before.forward after.sourceDomain)
        before.sourceDomain :=
    Set.ext fun _ => ⟨fun member => ⟨member.2, member.1⟩,
      fun member => ⟨member.2, member.1⟩⟩
  have sameTarget : (before.trans after).targetDomain =
      Set.inter (Set.preimage after.inverse before.targetDomain)
        after.targetDomain :=
    Set.ext fun _ => ⟨fun member => ⟨member.2, member.1⟩,
      fun member => ⟨member.2, member.1⟩⟩
  have carried : (targetReference.restrict after.sourceDomain).AEEq
      (ennrealIndicator before.targetDomain
        (fun value => ENNReal.ofReal (beforeFactor value)))
      (fun value => returnedWeight (after.forward value)) := by
    apply (Measure.ae_restrict_mem targetReference after.sourceMeasurable).mono
    intro value inside
    change ennrealIndicator before.targetDomain
        (fun value => ENNReal.ofReal (beforeFactor value)) value =
      ennrealIndicator (Set.preimage after.inverse before.targetDomain)
        (fun value => ENNReal.ofReal (beforeFactor (after.inverse value)))
        (after.forward value)
    unfold ennrealIndicator ennrealPiecewise Set.preimage
    dsimp only
    rw [after.inverse_forward value inside]
  have multiplied : (thirdReference.restrict after.targetDomain).AEEq
      (fun value => ENNReal.mul (ENNReal.ofReal (afterFactor value))
        (returnedWeight value))
      (ennrealIndicator (Set.preimage after.inverse before.targetDomain)
        (fun value => ENNReal.ofReal (Construction.Dedekind.mul (afterFactor value)
          (beforeFactor (after.inverse value))))) := by
    apply (Measure.ae_restrict_mem thirdReference after.targetMeasurable).mono
    intro value inside
    change ENNReal.mul (ENNReal.ofReal (afterFactor value))
        (ennrealIndicator (Set.preimage after.inverse before.targetDomain)
          (fun value => ENNReal.ofReal (beforeFactor (after.inverse value))) value) =
      ennrealIndicator (Set.preimage after.inverse before.targetDomain)
        (fun value => ENNReal.ofReal (Construction.Dedekind.mul (afterFactor value)
          (beforeFactor (after.inverse value)))) value
    unfold ennrealIndicator ennrealPiecewise
    by_cases member : Set.preimage after.inverse before.targetDomain value
    · rw [ite_eq_left member, ite_eq_left member]
      dsimp only
      rw [Real.ofReal_mul (afterNonnegative value inside)
          (beforeNonnegative _ member)]
    · rw [ite_eq_right member, ite_eq_right member, ENNReal.mul_zero]
  unfold ReferenceChange at beforeChange afterChange ⊢
  change (sourceReference.restrict (before.trans after).sourceDomain).map
      (fun value => after.forward (before.forward value))
      (MeasurableMap.comp after.forwardMeasurable before.forwardMeasurable) =
    (thirdReference.restrict (before.trans after).targetDomain).withDensity
      (fun value => ENNReal.ofReal (Construction.Dedekind.mul (afterFactor value)
        (beforeFactor (after.inverse value))))
  rw [sameSource,
    ← Measure.restrict_restrict _ _ (before.forwardMeasurable after.sourceMeasurable),
    ← Measure.map_comp _ before.forward after.forward before.forwardMeasurable
      after.forwardMeasurable, Measure.map_restrict _ _ _ after.sourceMeasurable,
    beforeChange, ← Measure.withDensity_restrict _ _ after.sourceMeasurable,
    Measure.restrict_restrict _ _ after.sourceMeasurable,
    Set.inter_comm after.sourceDomain before.targetDomain,
    ← Measure.restrict_restrict _ _ before.targetMeasurable,
    ← Measure.withDensity_indicator _ _ before.targetMeasurable,
    Measure.withDensity_congr_ae carried,
    Measure.map_withDensity _ after.forward after.forwardMeasurable
      returnedWeightMeasurable,
    afterChange, Measure.withDensity_withDensity _ afterWeight returnedWeightMeasurable,
    Measure.withDensity_congr_ae multiplied,
    Measure.withDensity_indicator _ _ returnedMeasurable,
    Measure.restrict_restrict _ _ returnedMeasurable, sameTarget]

/-- A reference change carries a factor that rides along unchanged. -/
public theorem reference_change_productRight {δ : Type w} {rest : Space δ}
    {pairing : MeasurablePartialEquivalence source target}
    {sourceReference : Measure source} {targetReference : Measure target}
    {factor : β → Real.Carrier}
    (restReference : Measure rest) (restFinite : Measure.SFinite restReference)
    (factorMeasurable : MeasurableMap target Real.borel factor)
    (change : pairing.ReferenceChange sourceReference targetReference factor) :
    (pairing.productRight rest).ReferenceChange
      (Measure.prod sourceReference restReference restFinite)
      (Measure.prod targetReference restReference restFinite)
      (fun value => factor value.1) := by
  have weightMeasurable : ENNRealMeasurable target
      (fun value => ENNReal.ofReal (factor value)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) Real.ofReal_measurable
      factorMeasurable
  unfold ReferenceChange at change ⊢
  change ((Measure.prod sourceReference restReference restFinite).restrict
      (fun input => pairing.sourceDomain input.1)).map
      (fun input => (pairing.forward input.1, input.2))
      (Space.product_map pairing.forwardMeasurable (MeasurableMap.identity rest)) =
    ((Measure.prod targetReference restReference restFinite).restrict
      (fun input => pairing.targetDomain input.1)).withDensity
      (fun value => ENNReal.ofReal (factor value.1))
  rw [Measure.prod_restrict_left _ _ _ pairing.sourceMeasurable,
    ← Measure.prod_map_left _ _ _ pairing.forward pairing.forwardMeasurable, change,
    Measure.prod_withDensity_left _ _ _ weightMeasurable,
    Measure.prod_restrict_left _ _ _ pairing.targetMeasurable]

end MeasurablePartialEquivalence

end
end Problib.Measure
