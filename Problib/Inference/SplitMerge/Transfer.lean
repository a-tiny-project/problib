module

public import Problib.Inference.SplitMerge.List
public import Problib.Inference.SplitMerge.Move
public import Problib.Measure.Product.Countable
public import Problib.Measure.Additive.Counting

set_option autoImplicit false

/-!
# Moving one entry between two lists

The transfer at positions `(i, j)` takes entry `i` out of the first list and
inserts it at position `j` of the second (`transferMember`). The reverse takes
entry `j` of the second list back to position `i` of the first. The auxiliary
carries `(i, j)` on both sides, and the pairing keeps it
(`SplitMergeMove.transfer`).

Against configuration references with coefficients `c` and `c′` and counting
on the positions, the first list shrinks from `n′ + 1` to `n′` and the second
grows from `m′ − 1` to `m′`. The factor is `c(n′ + 1) / c(n′)` times
`c′(m′ − 1) / c′(m′)` (`SplitMergeMove.transfer_reference_change`).
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel inverse_measurable measurable_mul)

universe u v w

public section

/-- Positions on each list. -/
abbrev positionPair : Space (Nat × Nat) := Space.product (Space.discrete Nat) (Space.discrete Nat)

/-- Counting on each pair of positions. -/
@[expose] noncomputable def positionPairCounting : Measure positionPair :=
  Measure.prod Measure.counting Measure.counting Measure.countingSigmaFinite.toSFinite

noncomputable def positionPairCountingFinite : Measure.SFinite positionPairCounting :=
  Measure.countingSigmaFinite.toSFinite.prod Measure.countingSigmaFinite.toSFinite

private theorem nat_injective : Function.Injective (fun index : Nat => index) :=
  fun _ _ same => same

/-- A set on a product with a pair of positions is measurable when each
section is measurable. -/
theorem positionPair_set_measurable {β : Type v} {source : Space β}
    {sets : Nat × Nat → Set β} (measurable : ∀ pair, source.Measurable (sets pair)) :
    (Space.product positionPair source).Measurable
      (fun input : (Nat × Nat) × β => sets input.1 input.2) := by
  have inner : ∀ first, (Space.product (Space.discrete Nat) source).Measurable
      (fun input : Nat × β => sets (first, input.1) input.2) := fun first =>
    MeasurableMap.set_uncurry_of_countable_first (fun index : Nat => index) nat_injective
      (sets := fun second => sets (first, second)) (fun second => measurable (first, second))
  have outer := MeasurableMap.set_uncurry_of_countable_first (fun index : Nat => index)
    nat_injective (sets := fun first (input : Nat × β) => sets (first, input.1) input.2) inner
  exact Space.associate_measurable (Space.discrete Nat) (Space.discrete Nat) source outer

/-- A map on a product with a pair of positions is measurable when each
section is measurable. -/
theorem positionPair_uncurry_measurable {β : Type v} {γ : Type w} {source : Space β}
    {target : Space γ} {function : Nat × Nat → β → γ}
    (measurable : ∀ pair, MeasurableMap source target (function pair)) :
    MeasurableMap (Space.product positionPair source) target
      (fun input : (Nat × Nat) × β => function input.1 input.2) :=
  MeasurableMap.comp
    (MeasurableMap.uncurry_of_countable_first (fun index : Nat => index) nat_injective
      (function := fun first (input : Nat × β) => function (first, input.1) input.2)
      (fun first => MeasurableMap.uncurry_of_countable_first (fun index : Nat => index)
        nat_injective (function := fun second => function (first, second))
        (fun second => measurable (first, second))))
    (Space.associate_measurable (Space.discrete Nat) (Space.discrete Nat) source)

variable {α : Type u} {element : Space α}

/-- Insert the one entry of the first list at a fixed position of the second. -/
@[expose] def insertLens (element : Space α) (position : Nat) :
    MeasurablePartialEquivalence (Space.product (Space.list element) (Space.list element))
      (Space.list element) :=
  (MeasurablePartialEquivalence.ofEquivalence
    (MeasurableEquivalence.swap (Space.list element) (Space.list element))).trans
    (scheduleLens element [position]).symm

/-- Take entry `removal` out of the first list and insert it at position
`insertion` of the second. -/
@[expose] def transferMember (element : Space α) (removal insertion : Nat) :
    MeasurablePartialEquivalence (Space.product (Space.list element) (Space.list element))
      (Space.product (Space.list element) (Space.list element)) :=
  (removeLens element [removal] (Space.list element)).trans
    ((insertLens element insertion).productLeft (Space.list element))

/-- Move one entry between two lists. The auxiliary carries the two positions,
and the reverse moves the entry back. -/
@[expose] def SplitMergeMove.transfer (element : Space α) :
    SplitMergeMove (Space.product (Space.list element) (Space.list element)) positionPair
      positionPair where
  pairing :=
    (MeasurablePartialEquivalence.ofEquivalence (MeasurableEquivalence.swap
        (Space.product (Space.list element) (Space.list element)) positionPair)).trans
      ((MeasurablePartialEquivalence.fibred positionPair
          (fun pair => transferMember element pair.1 pair.2)
          (positionPair_set_measurable
            (sets := fun pair => (transferMember element pair.1 pair.2).sourceDomain)
            (fun pair => (transferMember element pair.1 pair.2).sourceMeasurable))
          (positionPair_set_measurable
            (sets := fun pair => (transferMember element pair.1 pair.2).targetDomain)
            (fun pair => (transferMember element pair.1 pair.2).targetMeasurable))
          (positionPair_uncurry_measurable
            (function := fun pair => (transferMember element pair.1 pair.2).forward)
            (fun pair => (transferMember element pair.1 pair.2).forwardMeasurable))
          (positionPair_uncurry_measurable
            (function := fun pair => (transferMember element pair.1 pair.2).inverse)
            (fun pair => (transferMember element pair.1 pair.2).inverseMeasurable))).trans
        (MeasurablePartialEquivalence.ofEquivalence (MeasurableEquivalence.swap positionPair
          (Space.product (Space.list element) (Space.list element)))))

private theorem inverse_div (left right : Carrier) :
    Dedekind.inverse (Dedekind.div left right) = Dedekind.div right left := by
  rw [Dedekind.div_eq_mul_inverse, Dedekind.inverse_mul_total, Dedekind.inverse_inverse,
    Dedekind.div_eq_mul_inverse, Dedekind.mul_comm]

/-- The member's factor at a merge-side pair of lists: the reciprocal of the
second list's ratio before the insertion, times the first list's ratio. -/
@[expose] noncomputable def transferFactor (first second : Nat → NNReal) (insertion : Nat)
    (point : List α × List α) : Carrier :=
  Dedekind.mul
    (Dedekind.inverse (NNReal.toReal (coefficientRatio second 1 0
      (removeAll [insertion] point.2).1.length)))
    (NNReal.toReal (coefficientRatio first 1 0 point.1.length))

theorem transferFactor_measurable (first second : Nat → NNReal) (insertion : Nat) :
    MeasurableMap (Space.product (Space.list element) (Space.list element)) borel
      (transferFactor first second insertion) := by
  have remaining : MeasurableMap (Space.product (Space.list element) (Space.list element))
      (Space.discrete Nat) (fun point => (removeAll [insertion] point.2).1.length) :=
    MeasurableMap.comp (ListSpace.length_measurable element)
      (MeasurableMap.comp (Space.first_measurable _ _)
        (MeasurableMap.comp (removeAll_at_measurable element [insertion])
          (Space.second_measurable _ _)))
  have firstLength : MeasurableMap (Space.product (Space.list element) (Space.list element))
      (Space.discrete Nat) (fun point => point.1.length) :=
    MeasurableMap.comp (ListSpace.length_measurable element) (Space.first_measurable _ _)
  have reciprocal : MeasurableMap (Space.product (Space.list element) (Space.list element))
      borel (fun point => Dedekind.inverse (NNReal.toReal (coefficientRatio second 1 0
        (removeAll [insertion] point.2).1.length))) :=
    MeasurableMap.comp (MeasurableMap.from_discrete borel (fun length =>
      Dedekind.inverse (NNReal.toReal (coefficientRatio second 1 0 length)))) remaining
  have ratio : MeasurableMap (Space.product (Space.list element) (Space.list element))
      borel (fun point => NNReal.toReal (coefficientRatio first 1 0 point.1.length)) :=
    MeasurableMap.comp (MeasurableMap.from_discrete borel (fun length =>
      NNReal.toReal (coefficientRatio first 1 0 length))) firstLength
  intro set setMeasurable
  exact measurable_mul reciprocal ratio setMeasurable

theorem transferFactor_nonnegative {first second : Nat → NNReal}
    (secondNonzero : ∀ count, second count ≠ NNReal.zero) (insertion : Nat)
    (point : List α × List α) :
    Dedekind.le Dedekind.zero (transferFactor first second insertion point) :=
  Dedekind.mul_nonnegative
    (Dedekind.inverse_nonnegative
      (Dedekind.le_of_lt (coefficientRatio_positive secondNonzero _ _ _)))
    (coefficientRatio first 1 0 _).property

/-- Each transfer member changes reference by the first list's ratio at its
merge length, and the reciprocal of the second list's ratio at the length it
had before the insertion. -/
theorem transferMember_reference_change (reference : Measure element)
    (finite : Measure.SFinite reference) {first second : Nat → NNReal}
    (firstNonzero : ∀ count, first count ≠ NNReal.zero)
    (secondNonzero : ∀ count, second count ≠ NNReal.zero) (removal insertion : Nat) :
    (transferMember element removal insertion).ReferenceChange
      (Measure.prod (configurationReference reference finite first)
        (configurationReference reference finite second)
        (Measure.SFinite.configurationReference reference finite second))
      (Measure.prod (configurationReference reference finite first)
        (configurationReference reference finite second)
        (Measure.SFinite.configurationReference reference finite second))
      (transferFactor first second insertion) := by
  have firstFinite := Measure.SFinite.configurationReference reference finite first
  have secondFinite := Measure.SFinite.configurationReference reference finite second
  have singleFinite := Measure.SFinite.listPower finite 1
  have removing := removeLens_reference_change reference finite firstNonzero [removal]
    (configurationReference reference finite second) secondFinite
  have lensMeasurable := @first_length_measurable _ element _ (Space.list element)
    (fun length => NNReal.toReal (coefficientRatio second 1 0 length))
  have lens := scheduleLens_reference_change reference finite secondNonzero [insertion]
  have unlens := MeasurablePartialEquivalence.reference_change_symm lensMeasurable lens
    (fun _ _ => coefficientRatio_positive secondNonzero _ _ _)
  have unlensMeasurable : MeasurableMap (Space.list element) borel
      (fun values => Dedekind.inverse (NNReal.toReal (coefficientRatio second 1 0
        (removeAll [insertion] values).1.length))) :=
    MeasurableMap.comp inverse_measurable
      (MeasurableMap.comp lensMeasurable (scheduleLens element [insertion]).forwardMeasurable)
  have unlensNonnegative : ∀ values : List α, Dedekind.le Dedekind.zero
      (Dedekind.inverse (NNReal.toReal (coefficientRatio second 1 0
        (removeAll [insertion] values).1.length))) := fun _ =>
    Dedekind.inverse_nonnegative (Dedekind.le_of_lt (coefficientRatio_positive secondNonzero _ _ _))
  have inserting := MeasurePreserving.reference_change_before
    (MeasurePreserving.swap (Measure.listPower reference finite 1)
      (configurationReference reference finite second) singleFinite secondFinite)
    unlensMeasurable unlens (fun values _ => unlensNonnegative values)
  have beside := MeasurablePartialEquivalence.reference_change_productLeft
    (configurationReference reference finite first) (singleFinite.prod secondFinite)
    secondFinite unlensMeasurable inserting
  have removingMeasurable := @first_length_measurable _ element _
    (Space.product (Space.list element) (Space.list element))
    (fun length => NNReal.toReal (coefficientRatio first 1 0 length))
  exact MeasurablePartialEquivalence.reference_change_trans removingMeasurable
    (MeasurableMap.comp unlensMeasurable (Space.second_measurable _ _)) removing beside
    (fun value _ => (coefficientRatio first 1 0 value.1.length).property)
    (fun value _ => unlensNonnegative value.2)

/-- The transfer changes reference by `c(n′ + 1) / c(n′)` on the first list
and `c′(m′ − 1) / c′(m′)` on the second, at merge-side lengths `n′` and `m′`. -/
theorem SplitMergeMove.transfer_reference_change (reference : Measure element)
    (finite : Measure.SFinite reference) {first second : Nat → NNReal}
    (firstNonzero : ∀ count, first count ≠ NNReal.zero)
    (secondNonzero : ∀ count, second count ≠ NNReal.zero) :
    (SplitMergeMove.transfer element).pairing.ReferenceChange
      (Measure.prod
        (Measure.prod (configurationReference reference finite first)
          (configurationReference reference finite second)
          (Measure.SFinite.configurationReference reference finite second))
        positionPairCounting positionPairCountingFinite)
      (Measure.prod
        (Measure.prod (configurationReference reference finite first)
          (configurationReference reference finite second)
          (Measure.SFinite.configurationReference reference finite second))
        positionPairCounting positionPairCountingFinite)
      (fun point => Dedekind.mul (NNReal.toReal (coefficientRatio first 1 0 point.1.1.length))
        (NNReal.toReal (coefficientRatio second 0 1 point.1.2.length))) := by
  have firstFinite := Measure.SFinite.configurationReference reference finite first
  have secondFinite := Measure.SFinite.configurationReference reference finite second
  have stateFinite := firstFinite.prod secondFinite
  have memberMeasurable : MeasurableMap
      (Space.product positionPair (Space.product (Space.list element) (Space.list element)))
      borel (fun point => transferFactor first second point.1.2 point.2) :=
    positionPair_uncurry_measurable
      (function := fun pair => transferFactor first second pair.2)
      (fun pair => transferFactor_measurable first second pair.2)
  have fibre := MeasurablePartialEquivalence.reference_change_fibred positionPair
    (positionPair_set_measurable
      (sets := fun pair => (transferMember element pair.1 pair.2).sourceDomain)
      (fun pair => (transferMember element pair.1 pair.2).sourceMeasurable))
    (positionPair_set_measurable
      (sets := fun pair => (transferMember element pair.1 pair.2).targetDomain)
      (fun pair => (transferMember element pair.1 pair.2).targetMeasurable))
    (positionPair_uncurry_measurable
      (function := fun pair => (transferMember element pair.1 pair.2).forward)
      (fun pair => (transferMember element pair.1 pair.2).forwardMeasurable))
    (positionPair_uncurry_measurable
      (function := fun pair => (transferMember element pair.1 pair.2).inverse)
      (fun pair => (transferMember element pair.1 pair.2).inverseMeasurable))
    positionPairCounting stateFinite stateFinite
    (factor := fun pair => transferFactor first second pair.2)
    memberMeasurable
    (fun pair => transferMember_reference_change reference finite firstNonzero secondNonzero
      pair.1 pair.2)
  have leaving := MeasurePreserving.reference_change_after
    (MeasurePreserving.swap positionPairCounting
      (Measure.prod (configurationReference reference finite first)
        (configurationReference reference finite second) secondFinite)
      positionPairCountingFinite stateFinite)
    memberMeasurable fibre
    (fun point _ => transferFactor_nonnegative secondNonzero point.1.2 point.2)
  have whole := MeasurePreserving.reference_change_before
    (MeasurePreserving.swap
      (Measure.prod (configurationReference reference finite first)
        (configurationReference reference finite second) secondFinite)
      positionPairCounting stateFinite positionPairCountingFinite)
    (MeasurableMap.comp memberMeasurable (Space.swap_measurable _ _)) leaving
    (fun point _ => transferFactor_nonnegative secondNonzero point.2.2 point.1)
  refine MeasurablePartialEquivalence.reference_change_congr (fun point inside => ?_) whole
  have valid : ValidRemoval [point.2.2] point.1.2.length := inside.1.2.1.1
  have lengths := (removeAll_length valid).1
  change transferFactor first second point.2.2 point.1 = _
  unfold transferFactor
  rw [lengths, Dedekind.mul_comm]
  congr 1
  have positive : 1 ≤ point.1.2.length := by
    have below := valid.1
    omega
  unfold coefficientRatio
  rw [NNReal.toReal_div, NNReal.toReal_div, inverse_div]
  have shifted : point.1.2.length - [point.2.2].length + 1 - 0 = point.1.2.length := by
    simp only [List.length_cons, List.length_nil]
    omega
  have lowered : point.1.2.length + 0 - 1 = point.1.2.length - [point.2.2].length := by
    simp only [List.length_cons, List.length_nil]
    omega
  rw [shifted, lowered]

end
end Problib.Inference
