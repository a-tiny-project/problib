module

public import Problib.Inference.SplitMerge.Lens

set_option autoImplicit false

/-!
# One entry into two

A pairing that takes one entry with a draw to two entries with a residual acts
on lists: the list of one entry goes to the list of the two
(`oneTwoPairing`). The front lens peels the entries off and sets them back.
On ordered iid powers of lengths one and two, the list pairing changes
reference by the pairing's factor at the two leading entries
(`oneTwoPairing_reference_change`).
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel measurable_mul)
open Problib.Measure.ListSpace (coordinate)

universe u v w

variable {α : Type u} {ρ : Type v} {σ : Type w}
  {element : Space α} {draws : Space ρ} {residual : Space σ}

public section

/-- The entry at a position, or the fallback past the end. -/
@[expose] def entryAt (fallback : α) (index : Nat) (values : List α) : α :=
  Sum.elim (fun _ => fallback) (fun value => value) (coordinate index values)

theorem entryAt_measurable (element : Space α) (fallback : α) (index : Nat) :
    MeasurableMap (Space.list element) element (entryAt fallback index) :=
  MeasurableMap.comp
    (MeasurableMap.sum_elim (MeasurableMap.constant _ element fallback)
      (MeasurableMap.identity element))
    (MeasurableMap.comp (coordinate_at_measurable element)
      (Space.pair_measurable (MeasurableMap.identity _)
        (MeasurableMap.constant _ (Space.discrete Nat) index)))

/-- The two leading entries, with the fallback past the end. -/
@[expose] def leadingPair (fallback : α) (values : List α) : α × α :=
  (entryAt fallback 0 values, entryAt fallback 1 values)

theorem leadingPair_measurable (element : Space α) (fallback : α) :
    MeasurableMap (Space.list element) (Space.product element element) (leadingPair fallback) :=
  Space.pair_measurable (entryAt_measurable element fallback 0)
    (entryAt_measurable element fallback 1)

private theorem entryAt_eraseIdx (fallback : α) (values : List α) :
    entryAt fallback 0 (values.eraseIdx 0) = entryAt fallback 1 values := by
  cases values <;> rfl

/-- Take the one entry off the front, pass it with the draw through the
pairing, and set the two outputs back as a list beside the residual. -/
@[expose] def oneTwoPairing (fallback : α)
    (pairing : MeasurablePartialEquivalence (Space.product element draws)
      (Space.product (Space.product element element) residual)) :
    MeasurablePartialEquivalence (Space.product (Space.list element) draws)
      (Space.product (Space.list element) residual) :=
  ((frontLens element fallback 0).productRight draws).trans
    ((MeasurablePartialEquivalence.ofEquivalence
        (MeasurableEquivalence.commuteRight element (Space.list element) draws)).trans
      ((pairing.productRight (Space.list element)).trans
        ((MeasurablePartialEquivalence.ofEquivalence
            ((MeasurableEquivalence.commuteRight (Space.product element element) residual
                (Space.list element)).trans
              ((MeasurableEquivalence.associate element element (Space.list element)).product
                (MeasurableEquivalence.identity residual)))).trans
          ((((frontLens element fallback 0).symm.productLeft element).productRight
              residual).trans
            ((frontLens element fallback 0).symm.productRight residual)))))

/-- A merge-side point of the list pairing has its leading pair in the
pairing's range. -/
theorem oneTwoPairing_target_leading {fallback : α}
    {pairing : MeasurablePartialEquivalence (Space.product element draws)
      (Space.product (Space.product element element) residual)}
    {point : List α × σ} (inside : (oneTwoPairing fallback pairing).targetDomain point) :
    pairing.targetDomain (leadingPair fallback point.1, point.2) := by
  have paired : pairing.targetDomain
      ((entryAt fallback 0 point.1, entryAt fallback 0 (point.1.eraseIdx 0)), point.2) :=
    inside.1.1.2
  rw [entryAt_eraseIdx] at paired
  exact paired

/-- On the ordered iid powers of lengths one and two, the list pairing changes
reference by the pairing's factor at the two leading entries. -/
theorem oneTwoPairing_reference_change (reference : Measure element)
    (finite : Measure.SFinite reference) (fallback : α)
    {pairing : MeasurablePartialEquivalence (Space.product element draws)
      (Space.product (Space.product element element) residual)}
    {drawReference : Measure draws} (drawFinite : Measure.SFinite drawReference)
    {residualReference : Measure residual} (residualFinite : Measure.SFinite residualReference)
    {factor : (α × α) × σ → Carrier}
    (factorMeasurable : MeasurableMap (Space.product (Space.product element element) residual)
      borel factor)
    (factorNonnegative : ∀ value, pairing.targetDomain value →
      Dedekind.le Dedekind.zero (factor value))
    (change : pairing.ReferenceChange (Measure.prod reference drawReference drawFinite)
      (Measure.prod (Measure.prod reference reference finite) residualReference residualFinite)
      factor) :
    (oneTwoPairing fallback pairing).ReferenceChange
      (Measure.prod (Measure.listPower reference finite 1) drawReference drawFinite)
      (Measure.prod (Measure.listPower reference finite 2) residualReference residualFinite)
      (fun point => factor (leadingPair fallback point.1, point.2)) := by
  have unitNonnegative : Dedekind.le Dedekind.zero Dedekind.one :=
    Dedekind.le_of_lt Dedekind.one_positive
  have front0 := frontLens_reference_change reference finite fallback 0 0
  have front1 := frontLens_reference_change reference finite fallback 1 0
  have back0 := MeasurablePartialEquivalence.reference_change_congr
    (fun _ _ => Dedekind.inverse_one)
    (MeasurablePartialEquivalence.reference_change_symm
      (MeasurableMap.constant _ borel Dedekind.one) front0
      (fun _ _ => Dedekind.one_positive))
  have back1 := MeasurablePartialEquivalence.reference_change_congr
    (fun _ _ => Dedekind.inverse_one)
    (MeasurablePartialEquivalence.reference_change_symm
      (MeasurableMap.constant _ borel Dedekind.one) front1
      (fun _ _ => Dedekind.one_positive))
  have last := MeasurablePartialEquivalence.reference_change_productRight residualReference
    residualFinite (MeasurableMap.constant _ borel Dedekind.one) back1
  have second := MeasurablePartialEquivalence.reference_change_productRight residualReference
    residualFinite (MeasurableMap.constant _ borel Dedekind.one)
    (MeasurablePartialEquivalence.reference_change_productLeft reference
      (finite.prod (Measure.SFinite.listPower finite 0)) (Measure.SFinite.listPower finite 1)
      (MeasurableMap.constant _ borel Dedekind.one) back0)
  have setting := MeasurablePartialEquivalence.reference_change_congr
    (fun _ _ => Dedekind.mul_one Dedekind.one)
    (MeasurablePartialEquivalence.reference_change_trans
      (MeasurableMap.constant _ borel Dedekind.one)
      (MeasurableMap.constant _ borel Dedekind.one) second last
      (fun _ _ => unitNonnegative) (fun _ _ => unitNonnegative))
  have regrouped := MeasurePreserving.reference_change_before
    ((MeasurePreserving.commuteRight (Measure.prod reference reference finite)
        residualReference (Measure.listPower reference finite 0) residualFinite
        (Measure.SFinite.listPower finite 0)).trans
      (MeasurePreserving.product residualFinite residualFinite
        (MeasurePreserving.associate reference reference (Measure.listPower reference finite 0)
          finite (Measure.SFinite.listPower finite 0))
        (MeasurePreserving.refl residualReference)))
    (MeasurableMap.constant _ borel Dedekind.one) setting (fun _ _ => unitNonnegative)
  have paired := MeasurablePartialEquivalence.reference_change_productRight
    (Measure.listPower reference finite 0) (Measure.SFinite.listPower finite 0)
    factorMeasurable change
  have running := MeasurablePartialEquivalence.reference_change_trans
    (MeasurableMap.comp factorMeasurable (Space.first_measurable _ _))
    (MeasurableMap.constant _ borel Dedekind.one) paired regrouped
    (fun value inside => factorNonnegative _ inside) (fun _ _ => unitNonnegative)
  let setBack := (MeasurablePartialEquivalence.ofEquivalence
      ((MeasurableEquivalence.commuteRight (Space.product element element) residual
          (Space.list element)).trans
        ((MeasurableEquivalence.associate element element (Space.list element)).product
          (MeasurableEquivalence.identity residual)))).trans
    ((((frontLens element fallback 0).symm.productLeft element).productRight residual).trans
      ((frontLens element fallback 0).symm.productRight residual))
  have runningMeasurable : MeasurableMap (Space.product (Space.list element) residual) borel
      (fun value => Dedekind.mul Dedekind.one (factor (setBack.inverse value).1)) :=
    measurable_mul (MeasurableMap.constant _ borel Dedekind.one)
      (MeasurableMap.comp factorMeasurable
        (MeasurableMap.comp (Space.first_measurable _ _) setBack.inverseMeasurable))
  have runningNonnegative : ∀ value,
      ((pairing.productRight (Space.list element)).trans setBack).targetDomain value →
      Dedekind.le Dedekind.zero
        (Dedekind.mul Dedekind.one (factor (setBack.inverse value).1)) :=
    fun _ inside => Dedekind.mul_nonnegative unitNonnegative (factorNonnegative _ inside.2)
  have entering := MeasurePreserving.reference_change_before
    (MeasurePreserving.commuteRight reference (Measure.listPower reference finite 0)
      drawReference (Measure.SFinite.listPower finite 0) drawFinite)
    runningMeasurable running runningNonnegative
  have taking := MeasurablePartialEquivalence.reference_change_productRight drawReference
    drawFinite (MeasurableMap.constant _ borel Dedekind.one) front0
  have whole := MeasurablePartialEquivalence.reference_change_trans
    (MeasurableMap.constant _ borel Dedekind.one) runningMeasurable taking entering
    (fun _ _ => unitNonnegative) (fun value inside => runningNonnegative value inside.1)
  refine MeasurablePartialEquivalence.reference_change_congr (fun point _ => ?_) whole
  rcases point with ⟨values, residualValue⟩
  show Dedekind.mul (Dedekind.mul Dedekind.one
      (factor ((entryAt fallback 0 values, entryAt fallback 0 (values.eraseIdx 0)),
        residualValue))) Dedekind.one =
    factor (leadingPair fallback values, residualValue)
  rw [Dedekind.one_mul, Dedekind.mul_one, entryAt_eraseIdx]
  rfl

end
end Problib.Inference
