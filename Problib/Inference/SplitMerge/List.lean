module

public import Problib.Inference.SplitMerge.Lens

set_option autoImplicit false

/-!
# Replacing entries of a configuration

A move on a configuration takes `k` entries out along a removal schedule,
passes them with a residual through a pairing, and inserts the pairing's `l`
outputs along an insertion schedule (`replaceAt`). The merge side removes
along the reversed insertion schedule, so its removed entries, reversed, are
the pairing's outputs (`pairedElements`).

At a merge-side point of length `n′`, the split side had length
`n = n′ + k − l`. The reference change is the pairing's factor times
`c(n) / c(n′)` (`replaceAt_reference_change`). The two schedule lenses supply
`c(m + k) / c(m)` and its reciprocal at `c(m + l) / c(m)`, and the pairing
acts beside the remaining entries.
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel inverse_measurable measurable_mul)

universe u

variable {α ρ σ : Type u} {element : Space α}
  {splitResidual : Space ρ} {mergeResidual : Space σ}

public section

/-- Reverse a list. -/
@[expose] def reverseList (element : Space α) :
    MeasurableEquivalence (Space.list element) (Space.list element) where
  forward := List.reverse
  inverse := List.reverse
  inverse_forward := List.reverse_reverse
  forward_inverse := List.reverse_reverse
  forward_measurable := reverse_measurable element
  inverse_measurable := reverse_measurable element

/-- Reversal preserves each ordered iid power. -/
@[expose] noncomputable def reversePreserving (reference : Measure element)
    (finite : Measure.SFinite reference) (count : Nat) :
    MeasurePreserving (Measure.listPower reference finite count)
      (Measure.listPower reference finite count) where
  equivalence := reverseList element
  preserves := Measure.listPower_reverse reference finite count

/-- Reverse the list beside a residual. -/
@[expose] def reverseFirst (element : Space α) (residual : Space ρ) :
    MeasurableEquivalence (Space.product (Space.list element) residual)
      (Space.product (Space.list element) residual) :=
  (reverseList element).product (MeasurableEquivalence.identity residual)

/-- Take entries out along a removal schedule and set them beside the
residual. -/
@[expose] def removeLens (element : Space α) (positions : List Nat) (residual : Space ρ) :
    MeasurablePartialEquivalence (Space.product (Space.list element) residual)
      (Space.product (Space.list element) (Space.product (Space.list element) residual)) :=
  ((scheduleLens element positions).productRight residual).trans
    (MeasurablePartialEquivalence.ofEquivalence
      (MeasurableEquivalence.associate _ _ _))

/-- A function of the first list's length is measurable. -/
theorem first_length_measurable {β : Type u} (other : Space β) (factor : Nat → Carrier) :
    MeasurableMap (Space.product (Space.list element) other) borel
      (fun value => factor value.1.length) :=
  MeasurableMap.comp (MeasurableMap.from_discrete borel factor)
    (MeasurableMap.comp (ListSpace.length_measurable element) (Space.first_measurable _ _))

/-- Nonzero coefficients give a positive coefficient ratio. -/
theorem coefficientRatio_positive {coefficient : Nat → NNReal}
    (nonzero : ∀ count, coefficient count ≠ NNReal.zero) (removed inserted length : Nat) :
    Dedekind.lt Dedekind.zero
      (NNReal.toReal (coefficientRatio coefficient removed inserted length)) := by
  unfold coefficientRatio
  exact NNReal.div_positive ((NNReal.zero_lt_iff_ne_zero _).mpr (nonzero _))
    ((NNReal.zero_lt_iff_ne_zero _).mpr (nonzero _))

/-- The remove lens changes reference as its schedule lens does, with the
residual alongside. -/
theorem removeLens_reference_change (reference : Measure element)
    (finite : Measure.SFinite reference) {coefficient : Nat → NNReal}
    (nonzero : ∀ count, coefficient count ≠ NNReal.zero) (positions : List Nat)
    (residualReference : Measure splitResidual)
    (residualFinite : Measure.SFinite residualReference) :
    (removeLens element positions splitResidual).ReferenceChange
      (Measure.prod (configurationReference reference finite coefficient) residualReference
        residualFinite)
      (Measure.prod (configurationReference reference finite coefficient)
        (Measure.prod (Measure.listPower reference finite positions.length) residualReference
          residualFinite)
        ((Measure.SFinite.listPower finite positions.length).prod residualFinite))
      (fun value =>
        NNReal.toReal (coefficientRatio coefficient positions.length 0 value.1.length)) := by
  have ratioMeasurable := @first_length_measurable _ element _ (Space.list element)
    (fun length => NNReal.toReal (coefficientRatio coefficient positions.length 0 length))
  have lens := MeasurablePartialEquivalence.reference_change_productRight residualReference
    residualFinite ratioMeasurable
    (scheduleLens_reference_change reference finite nonzero positions)
  have whole := MeasurablePartialEquivalence.reference_change_trans
    (MeasurableMap.comp ratioMeasurable (Space.first_measurable _ _))
    (MeasurableMap.constant _ borel Dedekind.one) lens
    (MeasurePreserving.associate (configurationReference reference finite coefficient)
      (Measure.listPower reference finite positions.length) residualReference
      (Measure.SFinite.listPower finite positions.length) residualFinite).reference_change
    (fun value _ => (coefficientRatio coefficient positions.length 0 value.1.1.length).property)
    (fun _ _ => Dedekind.le_of_lt Dedekind.one_positive)
  refine MeasurablePartialEquivalence.reference_change_congr (fun value _ => ?_) whole
  change Dedekind.mul Dedekind.one
      (NNReal.toReal (coefficientRatio coefficient positions.length 0 value.1.length)) = _
  rw [Dedekind.one_mul]

/-- The merge side's paired entries: remove along the schedule, and reverse
the removed entries into insertion order. -/
@[expose] def pairedElements (positions : List Nat) (point : List α × σ) : List α × σ :=
  ((removeAll positions point.1).2.reverse, point.2)

/-- Remove along `removals`, pass the removed entries and the residual through
the pairing, and insert its outputs along `insertions`. -/
@[expose] def replaceAt (removals insertions : List Nat)
    (pairing : MeasurablePartialEquivalence
      (Space.product (Space.list element) splitResidual)
      (Space.product (Space.list element) mergeResidual)) :
    MeasurablePartialEquivalence (Space.product (Space.list element) splitResidual)
      (Space.product (Space.list element) mergeResidual) :=
  (removeLens element removals splitResidual).trans
    (((pairing.trans (MeasurablePartialEquivalence.ofEquivalence
        (reverseFirst element mergeResidual))).productLeft (Space.list element)).trans
      (removeLens element insertions.reverse mergeResidual).symm)

/-- The paired entries are measurable in the merge-side point. -/
theorem pairedElements_measurable (positions : List Nat) :
    MeasurableMap (Space.product (Space.list element) mergeResidual)
      (Space.product (Space.list element) mergeResidual) (pairedElements positions) :=
  MeasurableMap.comp (reverseFirst element mergeResidual).forward_measurable
    (MeasurableMap.comp (Space.second_measurable _ _)
      (removeLens element positions mergeResidual).forwardMeasurable)

/-- A merge-side point of the replacement has its paired entries in the
pairing's range. -/
theorem replaceAt_target_paired {removals insertions : List Nat}
    {pairing : MeasurablePartialEquivalence
      (Space.product (Space.list element) splitResidual)
      (Space.product (Space.list element) mergeResidual)}
    {point : List α × σ} (inside : (replaceAt removals insertions pairing).targetDomain point) :
    pairing.targetDomain (pairedElements insertions.reverse point) :=
  inside.1.2.2

private theorem ratio_cancel (merged base split factor : Carrier)
    (baseNonzero : base ≠ Dedekind.zero) :
    Dedekind.mul (Dedekind.mul (Dedekind.inverse (Dedekind.div merged base)) factor)
        (Dedekind.div split base) =
      Dedekind.mul factor (Dedekind.div split merged) := by
  rw [Dedekind.div_eq_mul_inverse merged base, Dedekind.inverse_mul_total,
    Dedekind.inverse_inverse, Dedekind.div_eq_mul_inverse split base,
    Dedekind.div_eq_mul_inverse split merged,
    Dedekind.mul_comm (Dedekind.mul (Dedekind.inverse merged) base) factor,
    Dedekind.mul_assoc factor]
  congr 1
  rw [Dedekind.mul_assoc (Dedekind.inverse merged) base, ← Dedekind.mul_assoc base split,
    Dedekind.mul_comm base split, Dedekind.mul_assoc split base,
    Dedekind.mul_inverse_cancel baseNonzero, Dedekind.mul_one, Dedekind.mul_comm]

/-- At a merge-side point of length `n′`, the split side had length
`n = n′ + k − l`, with `k` removed and `l` inserted. The reference change is
the pairing's factor at the paired entries times `c(n) / c(n′)`. Labelled
coefficients give one. Janossy coefficients give `n′! / n!`: a birth from
length `n` gives `n + 1`, and a death from length `n` gives `1 / n`. -/
theorem replaceAt_reference_change (reference : Measure element)
    (finite : Measure.SFinite reference) {coefficient : Nat → NNReal}
    (nonzero : ∀ count, coefficient count ≠ NNReal.zero) (removals insertions : List Nat)
    {pairing : MeasurablePartialEquivalence
      (Space.product (Space.list element) splitResidual)
      (Space.product (Space.list element) mergeResidual)}
    (splitReference : Measure splitResidual) (splitFinite : Measure.SFinite splitReference)
    (mergeReference : Measure mergeResidual) (mergeFinite : Measure.SFinite mergeReference)
    {factor : List α × σ → Carrier}
    (factorMeasurable : MeasurableMap (Space.product (Space.list element) mergeResidual) borel
      factor)
    (factorNonnegative : ∀ value, pairing.targetDomain value →
      Dedekind.le Dedekind.zero (factor value))
    (change : pairing.ReferenceChange
      (Measure.prod (Measure.listPower reference finite removals.length) splitReference
        splitFinite)
      (Measure.prod (Measure.listPower reference finite insertions.length) mergeReference
        mergeFinite) factor) :
    (replaceAt removals insertions pairing).ReferenceChange
      (Measure.prod (configurationReference reference finite coefficient) splitReference
        splitFinite)
      (Measure.prod (configurationReference reference finite coefficient) mergeReference
        mergeFinite)
      (fun point => Dedekind.mul (factor (pairedElements insertions.reverse point))
        (NNReal.toReal (coefficientRatio coefficient removals.length insertions.length
          point.1.length))) := by
  have unitMeasurable : ∀ {β : Type u} (space : Space β),
      MeasurableMap space borel (fun _ => Dedekind.one) := fun space =>
    MeasurableMap.constant space borel _
  have unitNonnegative : Dedekind.le Dedekind.zero Dedekind.one :=
    Dedekind.le_of_lt Dedekind.one_positive
  have removing := removeLens_reference_change reference finite nonzero removals
    splitReference splitFinite (coefficient := coefficient)
  have reversing := (MeasurePreserving.product mergeFinite mergeFinite
    (reversePreserving reference finite insertions.length)
    (MeasurePreserving.refl mergeReference)).reference_change
  have pairedMeasurable : MeasurableMap (Space.product (Space.list element) mergeResidual) borel
      (fun value => Dedekind.mul Dedekind.one
        (factor ((reverseFirst element mergeResidual).inverse value))) :=
    measurable_mul (unitMeasurable _)
      (MeasurableMap.comp factorMeasurable (reverseFirst element mergeResidual).inverse_measurable)
  have paired := MeasurablePartialEquivalence.reference_change_trans factorMeasurable
    (unitMeasurable _) change reversing factorNonnegative (fun _ _ => unitNonnegative)
  have beside := MeasurablePartialEquivalence.reference_change_productLeft
    (configurationReference reference finite coefficient)
    ((Measure.SFinite.listPower finite removals.length).prod splitFinite)
    ((Measure.SFinite.listPower finite insertions.length).prod mergeFinite)
    pairedMeasurable paired
  have inserting := removeLens_reference_change reference finite nonzero insertions.reverse
    mergeReference mergeFinite (coefficient := coefficient)
  rw [List.length_reverse] at inserting
  have insertingMeasurable := @first_length_measurable _ element _
    (Space.product (Space.list element) mergeResidual)
    (fun length => NNReal.toReal (coefficientRatio coefficient insertions.length 0 length))
  have unwinding := MeasurablePartialEquivalence.reference_change_symm insertingMeasurable
    inserting (fun value _ => coefficientRatio_positive nonzero _ _ _)
  have besideMeasurable : MeasurableMap
      (Space.product (Space.list element) (Space.product (Space.list element) mergeResidual))
      borel (fun value => Dedekind.mul Dedekind.one
        (factor ((reverseFirst element mergeResidual).inverse value.2))) :=
    MeasurableMap.comp pairedMeasurable (Space.second_measurable _ _)
  have unwindingMeasurable : MeasurableMap (Space.product (Space.list element) mergeResidual)
      borel (fun value => Dedekind.inverse (NNReal.toReal (coefficientRatio coefficient
        insertions.length 0
        ((removeLens element insertions.reverse mergeResidual).forward value).1.length))) :=
    MeasurableMap.comp inverse_measurable (MeasurableMap.comp insertingMeasurable
      (removeLens element insertions.reverse mergeResidual).forwardMeasurable)
  have later := MeasurablePartialEquivalence.reference_change_trans besideMeasurable
    unwindingMeasurable beside unwinding
    (fun value inside => by
      change Dedekind.le Dedekind.zero (Dedekind.mul Dedekind.one
        (factor ((reverseFirst element mergeResidual).inverse value.2)))
      rw [Dedekind.one_mul]
      exact factorNonnegative _ inside.2)
    (fun value _ => Dedekind.inverse_nonnegative (Dedekind.le_of_lt
      (coefficientRatio_positive nonzero _ _ _)))
  have removingMeasurable := @first_length_measurable _ element _
    (Space.product (Space.list element) splitResidual)
    (fun length => NNReal.toReal (coefficientRatio coefficient removals.length 0 length))
  have laterMeasurable : MeasurableMap (Space.product (Space.list element) mergeResidual) borel
      (fun value => Dedekind.mul
        (Dedekind.inverse (NNReal.toReal (coefficientRatio coefficient insertions.length 0
          ((removeLens element insertions.reverse mergeResidual).forward value).1.length)))
        (Dedekind.mul Dedekind.one (factor ((reverseFirst element mergeResidual).inverse
          ((removeLens element insertions.reverse mergeResidual).symm.inverse value).2)))) :=
    measurable_mul unwindingMeasurable (MeasurableMap.comp besideMeasurable
      (removeLens element insertions.reverse mergeResidual).forwardMeasurable)
  have whole := MeasurablePartialEquivalence.reference_change_trans
    removingMeasurable laterMeasurable
    removing later
    (fun value _ => (coefficientRatio coefficient removals.length 0 value.1.length).property)
    (fun value inside => by
      change Dedekind.le Dedekind.zero (Dedekind.mul
        (Dedekind.inverse (NNReal.toReal (coefficientRatio coefficient insertions.length 0
          ((removeLens element insertions.reverse mergeResidual).forward value).1.length)))
        (Dedekind.mul Dedekind.one (factor ((reverseFirst element mergeResidual).inverse
          ((removeLens element insertions.reverse mergeResidual).symm.inverse value).2))))
      rw [Dedekind.one_mul]
      exact Dedekind.mul_nonnegative
        (Dedekind.inverse_nonnegative (Dedekind.le_of_lt
          (coefficientRatio_positive nonzero _ _ _)))
        (factorNonnegative _ inside.2.2))
  refine MeasurablePartialEquivalence.reference_change_congr (fun point inside => ?_) whole
  have valid : ValidRemoval insertions.reverse point.1.length := inside.1.1.1
  have lengths := (removeAll_length valid).1
  have enough := valid_removal_length valid
  rw [List.length_reverse] at lengths enough
  change Dedekind.mul
      (Dedekind.mul
        (Dedekind.inverse (NNReal.toReal (coefficientRatio coefficient insertions.length 0
          (removeAll insertions.reverse point.1).1.length)))
        (Dedekind.mul Dedekind.one (factor (pairedElements insertions.reverse point))))
      (NNReal.toReal (coefficientRatio coefficient removals.length 0
        (removeAll insertions.reverse point.1).1.length)) = _
  generalize restLength : (removeAll insertions.reverse point.1).1.length = rest at lengths ⊢
  have total : point.1.length = rest + insertions.length := by omega
  have shifted : rest + insertions.length + removals.length - insertions.length =
      rest + removals.length := by omega
  rw [Dedekind.one_mul, total]
  unfold coefficientRatio
  rw [Nat.sub_zero, Nat.sub_zero, shifted, NNReal.toReal_div, NNReal.toReal_div,
    NNReal.toReal_div]
  exact ratio_cancel _ _ _ _ (NNReal.toReal_ne_zero (nonzero rest))

end
end Problib.Inference
