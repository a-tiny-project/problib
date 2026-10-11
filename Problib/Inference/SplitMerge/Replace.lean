module

public import Problib.Inference.SplitMerge.List
public import Problib.Inference.SplitMerge.Move
public import Problib.Measure.Equivalence.Fibred
public import Problib.Measure.Additive.Counting

set_option autoImplicit false

/-!
# Schedule-indexed replacement

The split side of `SplitMergeMove.replace` carries a removal schedule, an
insertion schedule and a residual. A split-side point `(x, ((is, js), r))`
pairs with the merge-side point `(x′, ((js.reverse, is.reverse), s))`, where
`(x′, s)` is `replaceAt is js pairing` at `(x, r)`. Schedules whose lengths are
not the removed and inserted counts pair nothing (`guarded`).

Schedules take the counting reference on lists of positions
(`positionCounting`), which reversal preserves. The replacement then changes
the configuration reference by the pairing's factor at the paired entries
times `c(n) / c(n′)` (`SplitMergeMove.replace_reference_change`). The proof
acts fibre by fibre over the schedules (`reference_change_fibred`), with
`replaceAt_reference_change` on each fibre.
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel measurable_mul)

universe u v w

public section

/-- Finite lists of positions, discrete in each entry. -/
abbrev positionSpace : Space (List Nat) := Space.list (Space.discrete Nat)

/-- A removal schedule and an insertion schedule. -/
abbrev schedulePair : Space (List Nat × List Nat) := Space.product positionSpace positionSpace

/-- Counting on each length of schedule. -/
@[expose] noncomputable def scheduleCounting : Measure positionSpace :=
  configurationReference Measure.counting Measure.countingSigmaFinite.toSFinite labelled

noncomputable def scheduleCountingFinite : Measure.SFinite scheduleCounting :=
  Measure.SFinite.configurationReference Measure.counting
    Measure.countingSigmaFinite.toSFinite labelled

/-- Counting on pairs of schedules. -/
@[expose] noncomputable def positionCounting : Measure schedulePair :=
  Measure.prod scheduleCounting scheduleCounting scheduleCountingFinite

noncomputable def positionCountingFinite : Measure.SFinite positionCounting :=
  scheduleCountingFinite.prod scheduleCountingFinite

/-- A set on a product with a schedule pair is measurable when each section
is measurable. -/
theorem schedules_set_measurable {β : Type v} {source : Space β}
    {sets : List Nat × List Nat → Set β}
    (measurable : ∀ schedules, source.Measurable (sets schedules)) :
    (Space.product schedulePair source).Measurable (fun input => sets input.1 input.2) := by
  have inner : ∀ removals, (Space.product positionSpace source).Measurable
      (fun input => sets (removals, input.1) input.2) := fun removals =>
    positions_uncurry_set_measurable (sets := fun insertions => sets (removals, insertions))
      (fun insertions => measurable (removals, insertions))
  have outer := positions_uncurry_set_measurable
    (sets := fun removals (input : List Nat × β) => sets (removals, input.1) input.2) inner
  exact Space.associate_measurable positionSpace positionSpace source outer

/-- A map on a product with a schedule pair is measurable when each section is
measurable. -/
theorem schedules_uncurry_measurable {β : Type v} {γ : Type w} {source : Space β}
    {target : Space γ} {function : List Nat × List Nat → β → γ}
    (measurable : ∀ schedules, MeasurableMap source target (function schedules)) :
    MeasurableMap (Space.product schedulePair source) target
      (fun input => function input.1 input.2) :=
  MeasurableMap.comp
    (positions_uncurry_measurable
      (function := fun removals (input : List Nat × β) => function (removals, input.1) input.2)
      (fun removals => positions_uncurry_measurable
        (function := fun insertions => function (removals, insertions))
        (fun insertions => measurable (removals, insertions))))
    (Space.associate_measurable positionSpace positionSpace source)

/-- Reverse both schedules and exchange them. -/
@[expose] def reverseSchedules : MeasurableEquivalence schedulePair schedulePair where
  forward := fun schedules => (schedules.2.reverse, schedules.1.reverse)
  inverse := fun schedules => (schedules.2.reverse, schedules.1.reverse)
  inverse_forward := fun schedules => by
    change (schedules.1.reverse.reverse, schedules.2.reverse.reverse) = schedules
    rw [List.reverse_reverse, List.reverse_reverse]
  forward_inverse := fun schedules => by
    change (schedules.1.reverse.reverse, schedules.2.reverse.reverse) = schedules
    rw [List.reverse_reverse, List.reverse_reverse]
  forward_measurable := Space.pair_measurable
    (MeasurableMap.comp (reverse_measurable _) (Space.second_measurable _ _))
    (MeasurableMap.comp (reverse_measurable _) (Space.first_measurable _ _))
  inverse_measurable := Space.pair_measurable
    (MeasurableMap.comp (reverse_measurable _) (Space.second_measurable _ _))
    (MeasurableMap.comp (reverse_measurable _) (Space.first_measurable _ _))

/-- Reversing and exchanging the schedules preserves the counting reference. -/
@[expose] noncomputable def reverseSchedulesPreserving :
    MeasurePreserving positionCounting positionCounting :=
  let reversal : MeasurePreserving scheduleCounting scheduleCounting :=
    { equivalence := reverseList (Space.discrete Nat)
      preserves := configurationReference_reverse Measure.counting
        Measure.countingSigmaFinite.toSFinite labelled }
  ((MeasurePreserving.swap scheduleCounting scheduleCounting scheduleCountingFinite
      scheduleCountingFinite).trans
    (MeasurePreserving.product scheduleCountingFinite scheduleCountingFinite reversal
      reversal)).congr reverseSchedules (fun _ => rfl)

section Guarded

variable {β : Type v} {γ : Type w} {source : Space β} {target : Space γ}

/-- A set cut down by a fixed proposition stays measurable. -/
theorem condition_and_measurable {space : Space β} (condition : Prop) {set : Set β}
    (measurable : space.Measurable set) :
    space.Measurable (fun value => condition ∧ set value) := by
  classical
  by_cases holds : condition
  · have equal : (fun value => condition ∧ set value) = set :=
      funext fun value => propext (and_iff_right holds)
    rw [equal]
    exact measurable
  · have equal : (fun value => condition ∧ set value) = Set.empty := by
      apply Set.ext
      intro value
      exact ⟨fun member => absurd member.1 holds, fun member => False.elim member⟩
    rw [equal]
    exact space.empty

/-- Keep the pairing where the condition holds, and pair nothing otherwise. -/
@[expose] def guarded (condition : Prop) (pairing : MeasurablePartialEquivalence source target) :
    MeasurablePartialEquivalence source target where
  forward := pairing.forward
  inverse := pairing.inverse
  sourceDomain := fun value => condition ∧ pairing.sourceDomain value
  targetDomain := fun value => condition ∧ pairing.targetDomain value
  sourceMeasurable := condition_and_measurable condition pairing.sourceMeasurable
  targetMeasurable := condition_and_measurable condition pairing.targetMeasurable
  forward_mem := fun value member => ⟨member.1, pairing.forward_mem value member.2⟩
  inverse_mem := fun value member => ⟨member.1, pairing.inverse_mem value member.2⟩
  inverse_forward := fun value member => pairing.inverse_forward value member.2
  forward_inverse := fun value member => pairing.forward_inverse value member.2
  forwardMeasurable := pairing.forwardMeasurable
  inverseMeasurable := pairing.inverseMeasurable

private theorem zero_withDensity (density : γ → ENNReal) :
    (Measure.zero target).withDensity density = Measure.zero target := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.withDensity_apply _ _ setMeasurable]
  have restricted : (Measure.zero target).restrict set = Measure.zero target := by
    apply Measure.ext
    intro other otherMeasurable
    rw [Measure.restrict_apply _ _ otherMeasurable, Measure.zero_apply, Measure.zero_apply]
  rw [restricted, lintegral_zero_measure, Measure.zero_apply]

/-- A guarded pairing changes reference as the pairing does where the
condition holds. Where it fails, both sides are zero. -/
theorem guarded_reference_change (condition : Prop)
    {pairing : MeasurablePartialEquivalence source target}
    {sourceReference : Measure source} {targetReference : Measure target}
    {factor : γ → Carrier}
    (change : condition → pairing.ReferenceChange sourceReference targetReference factor) :
    (guarded condition pairing).ReferenceChange sourceReference targetReference factor := by
  classical
  unfold MeasurablePartialEquivalence.ReferenceChange
  change (sourceReference.restrict (fun value => condition ∧ pairing.sourceDomain value)).map
      pairing.forward pairing.forwardMeasurable =
    (targetReference.restrict (fun value => condition ∧ pairing.targetDomain value)).withDensity
      (fun value => ENNReal.ofReal (factor value))
  by_cases holds : condition
  · have sourceSame : (fun value => condition ∧ pairing.sourceDomain value) =
        pairing.sourceDomain := funext fun value => propext (and_iff_right holds)
    have targetSame : (fun value => condition ∧ pairing.targetDomain value) =
        pairing.targetDomain := funext fun value => propext (and_iff_right holds)
    rw [sourceSame, targetSame]
    exact change holds
  · have sourceEmpty : (fun value => condition ∧ pairing.sourceDomain value) = Set.empty := by
      apply Set.ext
      intro value
      exact ⟨fun member => absurd member.1 holds, fun member => False.elim member⟩
    have targetEmpty : (fun value => condition ∧ pairing.targetDomain value) = Set.empty := by
      apply Set.ext
      intro value
      exact ⟨fun member => absurd member.1 holds, fun member => False.elim member⟩
    rw [sourceEmpty, targetEmpty, Measure.restrict_empty, Measure.restrict_empty,
      Measure.map_zero, zero_withDensity]

end Guarded

variable {α ρ σ : Type u} {element : Space α}
  {splitResidual : Space ρ} {mergeResidual : Space σ}

/-- The replacement at one pair of schedules, kept only when their lengths are
the removed and inserted counts. -/
@[expose] def replaceMember (removed inserted : Nat)
    (pairing : MeasurablePartialEquivalence
      (Space.product (Space.list element) splitResidual)
      (Space.product (Space.list element) mergeResidual))
    (schedules : List Nat × List Nat) :
    MeasurablePartialEquivalence (Space.product (Space.list element) splitResidual)
      (Space.product (Space.list element) mergeResidual) :=
  guarded (schedules.1.length = removed ∧ schedules.2.length = inserted)
    (replaceAt schedules.1 schedules.2 pairing)

section Member

variable (removed inserted : Nat)
  (pairing : MeasurablePartialEquivalence
    (Space.product (Space.list element) splitResidual)
    (Space.product (Space.list element) mergeResidual))

theorem replaceMember_source_measurable :
    (Space.product schedulePair (Space.product (Space.list element) splitResidual)).Measurable
      (fun point => (replaceMember removed inserted pairing point.1).sourceDomain point.2) :=
  schedules_set_measurable
    (fun schedules => (replaceMember removed inserted pairing schedules).sourceMeasurable)

theorem replaceMember_target_measurable :
    (Space.product schedulePair (Space.product (Space.list element) mergeResidual)).Measurable
      (fun point => (replaceMember removed inserted pairing point.1).targetDomain point.2) :=
  schedules_set_measurable
    (fun schedules => (replaceMember removed inserted pairing schedules).targetMeasurable)

theorem replaceMember_forward_measurable :
    MeasurableMap (Space.product schedulePair (Space.product (Space.list element) splitResidual))
      (Space.product (Space.list element) mergeResidual)
      (fun point => (replaceMember removed inserted pairing point.1).forward point.2) :=
  schedules_uncurry_measurable
    (fun schedules => (replaceMember removed inserted pairing schedules).forwardMeasurable)

theorem replaceMember_inverse_measurable :
    MeasurableMap (Space.product schedulePair (Space.product (Space.list element) mergeResidual))
      (Space.product (Space.list element) splitResidual)
      (fun point => (replaceMember removed inserted pairing point.1).inverse point.2) :=
  schedules_uncurry_measurable
    (fun schedules => (replaceMember removed inserted pairing schedules).inverseMeasurable)

end Member

/-- Remove `removed` entries along the first schedule, pass them through the
pairing, and insert its `inserted` outputs along the second. The merge side
carries the schedules reversed and exchanged. Birth and death is `(0, 1)`,
split and merge `(1, 2)`, and an update `(1, 1)`. -/
@[expose] def SplitMergeMove.replace (removed inserted : Nat)
    (pairing : MeasurablePartialEquivalence
      (Space.product (Space.list element) splitResidual)
      (Space.product (Space.list element) mergeResidual)) :
    SplitMergeMove (Space.list element) (Space.product schedulePair splitResidual)
      (Space.product schedulePair mergeResidual) where
  pairing :=
    ((MeasurablePartialEquivalence.ofEquivalence
        (MeasurableEquivalence.commuteLeft (Space.list element) schedulePair splitResidual)).trans
      (MeasurablePartialEquivalence.fibred schedulePair
        (replaceMember removed inserted pairing)
        (replaceMember_source_measurable removed inserted pairing)
        (replaceMember_target_measurable removed inserted pairing)
        (replaceMember_forward_measurable removed inserted pairing)
        (replaceMember_inverse_measurable removed inserted pairing))).trans
      (MeasurablePartialEquivalence.ofEquivalence
        ((reverseSchedules.product (MeasurableEquivalence.identity
            (Space.product (Space.list element) mergeResidual))).trans
          (MeasurableEquivalence.commuteLeft schedulePair (Space.list element) mergeResidual)))

/-- The replacement changes reference by the pairing's factor at the paired
entries, times `c(n) / c(n′)` at a merge-side point of length `n′`, with
`n = n′ + removed − inserted`. The merge side's first schedule locates the
paired entries. -/
theorem SplitMergeMove.replace_reference_change (reference : Measure element)
    (finite : Measure.SFinite reference) {coefficient : Nat → NNReal}
    (nonzero : ∀ count, coefficient count ≠ NNReal.zero) (removed inserted : Nat)
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
      (Measure.prod (Measure.listPower reference finite removed) splitReference splitFinite)
      (Measure.prod (Measure.listPower reference finite inserted) mergeReference mergeFinite)
      factor) :
    (SplitMergeMove.replace removed inserted pairing).pairing.ReferenceChange
      (Measure.prod (configurationReference reference finite coefficient)
        (Measure.prod positionCounting splitReference splitFinite)
        (positionCountingFinite.prod splitFinite))
      (Measure.prod (configurationReference reference finite coefficient)
        (Measure.prod positionCounting mergeReference mergeFinite)
        (positionCountingFinite.prod mergeFinite))
      (fun point => Dedekind.mul (factor (pairedElements point.2.1.1 (point.1, point.2.2)))
        (NNReal.toReal (coefficientRatio coefficient removed inserted point.1.length))) := by
  have configurationFinite := Measure.SFinite.configurationReference reference finite coefficient
  have unitMeasurable : ∀ {β : Type u} (space : Space β),
      MeasurableMap space borel (fun _ => Dedekind.one) := fun space =>
    MeasurableMap.constant space borel _
  have unitNonnegative : Dedekind.le Dedekind.zero Dedekind.one :=
    Dedekind.le_of_lt Dedekind.one_positive
  have members : ∀ schedules : List Nat × List Nat,
      (replaceMember removed inserted pairing schedules).ReferenceChange
        (Measure.prod (configurationReference reference finite coefficient) splitReference
          splitFinite)
        (Measure.prod (configurationReference reference finite coefficient) mergeReference
          mergeFinite)
        (fun point => Dedekind.mul (factor (pairedElements schedules.2.reverse point))
          (NNReal.toReal (coefficientRatio coefficient removed inserted point.1.length))) := by
    intro schedules
    apply guarded_reference_change
    intro lengths
    have result := replaceAt_reference_change reference finite nonzero schedules.1 schedules.2
      splitReference splitFinite mergeReference mergeFinite factorMeasurable factorNonnegative
      (coefficient := coefficient) (by rw [lengths.1, lengths.2]; exact change)
    rw [lengths.1, lengths.2] at result
    exact result
  have memberMeasurable : MeasurableMap
      (Space.product schedulePair (Space.product (Space.list element) mergeResidual)) borel
      (fun point => Dedekind.mul (factor (pairedElements point.1.2.reverse point.2))
        (NNReal.toReal (coefficientRatio coefficient removed inserted point.2.1.length))) :=
    schedules_uncurry_measurable
      (function := fun schedules point =>
        Dedekind.mul (factor (pairedElements schedules.2.reverse point))
          (NNReal.toReal (coefficientRatio coefficient removed inserted point.1.length)))
      (fun schedules => measurable_mul
        (MeasurableMap.comp factorMeasurable (pairedElements_measurable schedules.2.reverse))
        (first_length_measurable mergeResidual
          (fun length => NNReal.toReal (coefficientRatio coefficient removed inserted length))))
  have fibre := MeasurablePartialEquivalence.reference_change_fibred schedulePair
    (replaceMember_source_measurable removed inserted pairing)
    (replaceMember_target_measurable removed inserted pairing)
    (replaceMember_forward_measurable removed inserted pairing)
    (replaceMember_inverse_measurable removed inserted pairing)
    positionCounting (configurationFinite.prod splitFinite)
    (configurationFinite.prod mergeFinite)
    (factor := fun schedules point =>
      Dedekind.mul (factor (pairedElements schedules.2.reverse point))
        (NNReal.toReal (coefficientRatio coefficient removed inserted point.1.length)))
    memberMeasurable members
  have entering := (MeasurePreserving.commuteLeft
    (configurationReference reference finite coefficient) positionCounting splitReference
    configurationFinite positionCountingFinite splitFinite).reference_change
  have entered := MeasurablePartialEquivalence.reference_change_trans
    (unitMeasurable _) memberMeasurable entering fibre (fun _ _ => unitNonnegative)
    (fun point inside => Dedekind.mul_nonnegative
      (factorNonnegative _ (replaceAt_target_paired inside.2))
      (coefficientRatio coefficient removed inserted point.2.1.length).property)
  have leaving := ((MeasurePreserving.product (configurationFinite.prod mergeFinite)
      (configurationFinite.prod mergeFinite) reverseSchedulesPreserving
      (MeasurePreserving.refl (Measure.prod (configurationReference reference finite coefficient)
        mergeReference mergeFinite))).trans
    (MeasurePreserving.commuteLeft positionCounting
      (configurationReference reference finite coefficient) mergeReference
      positionCountingFinite configurationFinite mergeFinite)).reference_change
  have enteredMeasurable : MeasurableMap
      (Space.product schedulePair (Space.product (Space.list element) mergeResidual)) borel
      (fun point => Dedekind.mul
        (Dedekind.mul (factor (pairedElements point.1.2.reverse point.2))
          (NNReal.toReal (coefficientRatio coefficient removed inserted point.2.1.length)))
        Dedekind.one) :=
    measurable_mul memberMeasurable (unitMeasurable _)
  have whole := MeasurablePartialEquivalence.reference_change_trans
    enteredMeasurable (unitMeasurable _) entered leaving
    (fun point inside => by
      change Dedekind.le Dedekind.zero (Dedekind.mul
        (Dedekind.mul (factor (pairedElements point.1.2.reverse point.2))
          (NNReal.toReal (coefficientRatio coefficient removed inserted point.2.1.length)))
        Dedekind.one)
      rw [Dedekind.mul_one]
      exact Dedekind.mul_nonnegative
        (factorNonnegative _ (replaceAt_target_paired inside.1.2))
        (coefficientRatio coefficient removed inserted point.2.1.length).property)
    (fun _ _ => unitNonnegative)
  refine MeasurablePartialEquivalence.reference_change_congr (fun point _ => ?_) whole
  change Dedekind.mul Dedekind.one (Dedekind.mul
      (Dedekind.mul (factor (pairedElements point.2.1.1.reverse.reverse (point.1, point.2.2)))
        (NNReal.toReal (coefficientRatio coefficient removed inserted point.1.length)))
      Dedekind.one) = _
  rw [Dedekind.one_mul, Dedekind.mul_one, List.reverse_reverse]

end
end Problib.Inference
