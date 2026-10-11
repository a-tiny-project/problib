module

public import Problib.Measure.Equivalence.Preserving
public import Problib.Inference.Sequential
public import Problib.Measure.Configuration.Shuffle
public import Problib.Measure.Configuration.Power
public import Problib.Inference.SplitMerge.Matter
public import Problib.Inference.SplitMerge.Kernel

set_option autoImplicit false

/-!
# Stage index and cardinality

A sequential stage index counts stages, not elements. A birth stage from one
iid draw stays with probability one half and otherwise inserts a fresh draw at
a uniform position. It is an exact SeqRN stage with unit increment into the
even mixture of one and two draws (`birthStage_seq_rn`), so stage one carries
cardinality one or two.

Stage one has density one half on lengths one and two against the labelled
configuration reference (`stageOneDensity_represents`). A birth/death split/merge kernel
leaves it invariant, for any selection with a density.

A stage cannot put mass where its proposal puts none. So stages that add at
most one element each keep the count within the initial bound plus the number
of stages (`bounded_births_bounded_count`). A target with unbounded
cardinality therefore needs a move that changes the count within a stage.
-/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u

variable {α : Type u} {element : Space α}

public section

/-- Draw an element from the reference and insert it at a uniform position. -/
@[expose] noncomputable def birth (reference : Measure element)
    (finite : Measure.SFinite reference) :
    Kernel (Space.list element) (Space.list element) :=
  ((Kernel.attach (Kernel.const (Space.list element) reference)
      (Kernel.IsSFinite.const _ finite)).map (fun pair => (pair.2, pair.1))
      (Space.swap_measurable _ _)).comp (insertAtUniform element)

/-- The half weight of the birth stage. -/
@[expose] noncomputable def half : ENNReal := ENNReal.finite (NNReal.half NNReal.one)

/-- Stay with probability one half, and otherwise give birth. -/
@[expose] noncomputable def birthStage (reference : Measure element)
    (finite : Measure.SFinite reference) :
    Kernel (Space.list element) (Space.list element) :=
  Kernel.add (Kernel.smul half (Kernel.deterministic (fun values => values)
      (MeasurableMap.identity _)))
    (Kernel.smul half (birth reference finite))

theorem lintegral_birth (reference : Measure element) (finite : Measure.SFinite reference)
    {function : List α → ENNReal}
    (functionMeasurable : ENNRealMeasurable (Space.list element) function)
    (values : List α) :
    lintegral (birth reference finite values) function =
      lintegral reference (fun value =>
        lintegral (Measure.uniformBelow (values.length + 1))
          (fun position => function (values.insertIdx position value))) := by
  have drawn : birth reference finite values =
      (reference.map (fun value => (value, values))
        (Space.pair_measurable (MeasurableMap.identity element)
          (MeasurableMap.constant element (Space.list element) values))).bind
        (insertAtUniform element) := by
    change ((reference.map (fun value => (values, value))
        (Kernel.pair_left_measurable (source := Space.list element) (target := element)
          values)).map (fun pair => (pair.2, pair.1)) (Space.swap_measurable _ _)).bind
        (insertAtUniform element) = _
    rw [Measure.map_comp _ _ _ (Kernel.pair_left_measurable (source := Space.list element)
      (target := element) values) (Space.swap_measurable _ _)]
  rw [drawn, Measure.lintegral_bind _ _ functionMeasurable,
    lintegral_map _ _ _ ((insertAtUniform element).lintegral_measurable functionMeasurable)]
  apply lintegral_congr
  intro value
  change lintegral ((Measure.uniformBelow (values.length + 1)).map
      (fun position => values.insertIdx position value)
      (MeasurableMap.from_discrete (Space.list element)
        (fun position => values.insertIdx position value))) function = _
  rw [lintegral_map _ _ _ functionMeasurable]

/-- A birth from an iid power gives the next iid power. -/
theorem birth_power (reference : Measure element) (finite : Measure.SFinite reference)
    (count : Nat) :
    (Measure.listPower reference finite count).bind (birth reference finite) =
      Measure.listPower reference finite (count + 1) := by
  apply Measure.ext_of_lintegral
  intro function functionMeasurable
  let inserted : (List α × Nat) × α → ENNReal := fun input =>
    function (input.1.1.insertIdx input.1.2 input.2)
  have insertedMeasurable : ENNRealMeasurable
      (Space.product (Space.product (Space.list element) (Space.discrete Nat)) element)
      inserted :=
    ENNRealMeasurable.comp functionMeasurable (Measure.insertIdx_measurable element)
  have innerMeasurable : ENNRealMeasurable
      (Space.product (Space.list element) (Space.discrete Nat))
      (fun pair => lintegral reference (fun value => inserted (pair, value))) :=
    Kernel.lintegral_measurable_joint (Kernel.const _ reference)
      (Kernel.IsSFinite.const _ finite) (function := fun pair value => inserted (pair, value))
      insertedMeasurable
  have swapped : ∀ values : List α,
      lintegral reference (fun value =>
        lintegral (Measure.uniformBelow (count + 1))
          (fun position => function (values.insertIdx position value))) =
      lintegral (Measure.uniformBelow (count + 1)) (fun position =>
        lintegral reference (fun value => function (values.insertIdx position value))) := by
    intro values
    have pairing : MeasurableMap (Space.product element (Space.discrete Nat))
        (Space.product (Space.product (Space.list element) (Space.discrete Nat)) element)
        (fun pair : α × Nat => ((values, pair.2), pair.1)) :=
      Space.pair_measurable
        (Space.pair_measurable (MeasurableMap.constant _ _ values)
          (Space.second_measurable _ _))
        (Space.first_measurable _ _)
    have jointMeasurable : ENNRealMeasurable
        (Space.product element (Space.discrete Nat))
        (fun pair : α × Nat => function (values.insertIdx pair.2 pair.1)) :=
      ENNRealMeasurable.comp (map := inserted) insertedMeasurable pairing
    rw [← lintegral_prod reference (Measure.uniformBelow (count + 1))
        (Measure.uniformBelowSFinite (count + 1)) jointMeasurable,
      lintegral_prod_symm reference (Measure.uniformBelow (count + 1)) finite
        (Measure.uniformBelowSFinite (count + 1)) jointMeasurable]
  have lengthNull := Measure.listPower_length_null reference finite count
  have almost : (Measure.listPower reference finite count).AEEq
      (fun values => lintegral (birth reference finite values) function)
      (fun values => lintegral (Measure.uniformBelow (count + 1)) (fun position =>
        lintegral reference (fun value => function (values.insertIdx position value)))) := by
    have sameLength : (Measure.listPower reference finite count).AE
        (fun values : List α => values.length = count) :=
      Measure.NullSet.mono lengthNull (fun {_} failure => failure)
    refine sameLength.mono ?_
    intro values length
    show lintegral (birth reference finite values) function =
      lintegral (Measure.uniformBelow (count + 1)) (fun position =>
        lintegral reference (fun value => function (values.insertIdx position value)))
    rw [lintegral_birth reference finite functionMeasurable values, length]
    exact swapped values
  rw [Measure.lintegral_bind _ _ functionMeasurable, lintegral_congr_ae almost,
    ← Measure.insertion_uniform_power reference finite count,
    lintegral_map _ _ _ functionMeasurable,
    lintegral_prod _ reference finite insertedMeasurable,
    lintegral_prod _ _ (Measure.uniformBelowSFinite (count + 1)) innerMeasurable]

/-- Stage one from one iid draw: stay or give birth, with unit increment, is
an exact SeqRN stage into the even mixture of one and two draws. -/
theorem birthStage_seq_rn (reference : Measure element) (finite : Measure.SFinite reference) :
    SeqRN (Measure.listPower reference finite 1)
      (Measure.add (Measure.smul half (Measure.listPower reference finite 1))
        (Measure.smul half (Measure.listPower reference finite 2)))
      (birthStage reference finite) (fun _ => NNReal.one) := by
  intro function functionMeasurable
  have unit : ∀ values : List α, (fun value => ENNReal.mul (ENNReal.finite NNReal.one)
      (function value)) = function := fun _ => funext fun value => ENNReal.one_mul _
  have stage : ∀ values : List α,
      lintegral (birthStage reference finite values) function =
        ENNReal.add (ENNReal.mul half (function values))
          (ENNReal.mul half (lintegral (birth reference finite values) function)) := by
    intro values
    unfold birthStage
    rw [Kernel.add_apply, lintegral_add_measure, Kernel.smul_apply, Kernel.smul_apply,
      lintegral_smul_measure, lintegral_smul_measure,
      Kernel.deterministic_apply (fun values => values) (MeasurableMap.identity _),
      lintegral_dirac _ _ functionMeasurable]
  have dropUnit : (fun values => lintegral (birthStage reference finite values)
      (fun value => ENNReal.mul (ENNReal.finite NNReal.one) (function value))) =
      (fun values => lintegral (birthStage reference finite values) function) :=
    funext fun values => congrArg (lintegral (birthStage reference finite values)) (unit values)
  rw [dropUnit]
  have birthMeasurable : ENNRealMeasurable (Space.list element)
      (fun values => lintegral (birth reference finite values) function) :=
    (birth reference finite).lintegral_measurable functionMeasurable
  rw [lintegral_congr _ stage,
    lintegral_add _ (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _) functionMeasurable)
      (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _) birthMeasurable),
    lintegral_smul _ _ functionMeasurable, lintegral_smul _ _ birthMeasurable,
    ← Measure.lintegral_bind _ _ functionMeasurable, birth_power,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]

/-- A stage whose proposal adds at most one element carries a length bound
forward by one. -/
theorem seq_rn_length_bound {source target : Measure (Space.list element)}
    {proposal : Kernel (Space.list element) (Space.list element)}
    (proposalFinite : Kernel.IsSFinite proposal)
    {increment : List α × List α → NNReal}
    (incrementMeasurable : MeasurableMap
      (Space.product (Space.list element) (Space.list element)) weightSpace increment)
    (rn : SeqRN source target proposal increment)
    (adds : ∀ values, proposal values (fun next => values.length + 1 < next.length) =
      ENNReal.zero)
    {bound : Nat} (bounded : source (fun values => bound < values.length) = ENNReal.zero) :
    target (fun values => bound + 1 < values.length) = ENNReal.zero := by
  have regionMeasurable : (Space.list element).Measurable
      (fun values : List α => bound + 1 < values.length) :=
    ListSpace.length_measurable element (set := fun length => bound + 1 < length) trivial
  apply seq_rn_absolutely_continuous proposalFinite incrementMeasurable rn regionMeasurable
  rw [Measure.bind_apply _ _ regionMeasurable]
  apply lintegral_eq_zero_of_ae_zero
  have short : source.AE (fun values : List α => ¬ bound < values.length) :=
    Measure.NullSet.mono bounded (fun {_} failure => Classical.byContradiction failure)
  refine short.mono ?_
  intro values short
  apply ENNReal.le_antisymm _ (ENNReal.zero_le _)
  rw [← adds values]
  apply Measure.mono
  intro next longer
  omega

/-- Stages that each add at most one element keep the count within the initial
bound plus the number of stages. -/
theorem bounded_births_bounded_count (laws : Nat → Measure (Space.list element))
    (proposals : Nat → Kernel (Space.list element) (Space.list element))
    (proposalsFinite : ∀ stage, Kernel.IsSFinite (proposals stage))
    (increments : Nat → List α × List α → NNReal)
    (incrementsMeasurable : ∀ stage, MeasurableMap
      (Space.product (Space.list element) (Space.list element)) weightSpace (increments stage))
    (rn : ∀ stage, SeqRN (laws stage) (laws (stage + 1)) (proposals stage) (increments stage))
    (adds : ∀ stage values,
      proposals stage values (fun next => values.length + 1 < next.length) = ENNReal.zero)
    {initialBound : Nat}
    (bounded : laws 0 (fun values => initialBound < values.length) = ENNReal.zero)
    (stage : Nat) :
    laws stage (fun values => initialBound + stage < values.length) = ENNReal.zero := by
  induction stage with
  | zero => exact bounded
  | succ stage induction =>
      exact seq_rn_length_bound (proposalsFinite stage) (incrementsMeasurable stage)
        (rn stage) (adds stage) induction

section StageOne

open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel ofReal_measurable)

/-- One half on counts one and two, and zero elsewhere. -/
@[expose] noncomputable def stageOneWeight (count : Nat) : Carrier :=
  if count = 1 ∨ count = 2 then NNReal.toReal (NNReal.half NNReal.one) else Dedekind.zero

/-- The density of stage one against the labelled configuration reference. -/
@[expose] noncomputable def stageOneDensity (values : List α) : Carrier :=
  stageOneWeight values.length

private theorem ofReal_half : ENNReal.ofReal (NNReal.toReal (NNReal.half NNReal.one)) = half := by
  unfold ENNReal.ofReal half
  rw [NNReal.ofReal_toReal]

theorem stageOneDensity_measurable :
    MeasurableMap (Space.list element) borel (stageOneDensity (α := α)) :=
  MeasurableMap.comp (fun _ => Space.discrete_measurable _) (ListSpace.length_measurable element)

theorem stageOneDensity_nonnegative (values : List α) :
    Dedekind.le Dedekind.zero (stageOneDensity values) := by
  unfold stageOneDensity stageOneWeight
  split
  · exact (NNReal.half NNReal.one).property
  · exact Dedekind.le_refl _

/-- The even mixture of one and two draws has density one half on lengths one
and two against the labelled configuration reference. -/
theorem stageOneDensity_represents (reference : Measure element)
    (finite : Measure.SFinite reference) :
    Measure.add (Measure.smul half (Measure.listPower reference finite 1))
        (Measure.smul half (Measure.listPower reference finite 2)) =
      (configurationReference reference finite labelled).withDensity
        (fun values => ENNReal.ofReal (stageOneDensity values)) := by
  have densityMeasurable : ENNRealMeasurable (Space.list element)
      (fun values : List α => ENNReal.ofReal (stageOneDensity values)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable stageOneDensity_measurable
  apply Measure.ext
  intro set setMeasurable
  have indicatorMeasurable : ENNRealMeasurable (Space.list element)
      (ennrealIndicator set fun _ => ENNReal.one) :=
    ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)
  have power : ∀ count, lintegral (Measure.listPower reference finite count)
      (fun values => ENNReal.mul (ENNReal.ofReal (stageOneDensity values))
        (ennrealIndicator set (fun _ => ENNReal.one) values)) =
      ENNReal.mul (ENNReal.ofReal (stageOneWeight count))
        (Measure.listPower reference finite count set) := by
    intro count
    rw [apply_eq_lintegral_indicator (Measure.listPower reference finite count) setMeasurable,
      ← lintegral_smul _ _ indicatorMeasurable]
    apply lintegral_congr_ae
    exact Measure.NullSet.mono (Measure.listPower_length_null reference finite count)
      (fun {values} different sameLength => different (by
        show ENNReal.mul (ENNReal.ofReal (stageOneWeight values.length)) _ = _
        rw [sameLength]))
  have terms : (fun count => ENNReal.mul (ENNReal.finite (labelled count))
        (ENNReal.mul (ENNReal.ofReal (stageOneWeight count))
          (Measure.listPower reference finite count set))) =
      fun count => ENNReal.add
        (ENNReal.single 1 (ENNReal.mul half (Measure.listPower reference finite 1 set)) count)
        (ENNReal.single 2 (ENNReal.mul half (Measure.listPower reference finite 2 set)) count) := by
    funext count
    have unit : ENNReal.finite (labelled count) = ENNReal.one := rfl
    rw [unit, ENNReal.one_mul]
    unfold stageOneWeight ENNReal.single
    by_cases first : count = 1
    · subst first
      rw [ite_eq_left (Or.inl rfl), ite_eq_left rfl, ite_eq_right (by decide), ofReal_half,
        ENNReal.add_zero]
    · by_cases second : count = 2
      · subst second
        rw [ite_eq_left (Or.inr rfl), ite_eq_right (by decide), ite_eq_left rfl, ofReal_half,
          ENNReal.zero_add]
      · rw [ite_eq_right (fun either => either.elim first second), ite_eq_right first, ite_eq_right second,
          ENNReal.ofReal_zero, ENNReal.zero_mul, ENNReal.add_zero]
  rw [Measure.add_apply_measurable _ _ setMeasurable,
    Measure.smul_apply_measurable _ _ setMeasurable,
    Measure.smul_apply_measurable _ _ setMeasurable,
    apply_eq_lintegral_indicator
      ((configurationReference reference finite labelled).withDensity
        (fun values => ENNReal.ofReal (stageOneDensity values))) setMeasurable,
    lintegral_withDensity _ densityMeasurable indicatorMeasurable]
  unfold configurationReference
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, power]
  rw [terms, ENNReal.tsum_add, ENNReal.tsum_single, ENNReal.tsum_single]

/-- A birth/death split/merge kernel leaves stage one invariant, whatever the
selection, as long as it has a density. -/
example (reference : Measure element) (finite : Measure.SFinite reference)
    (births : SplitMergeSelection (Space.list element) _ _
      (Measure.prod positionCounting (Measure.listPower reference finite 1)
        (Measure.SFinite.listPower finite 1))
      (Measure.prod positionCounting (Measure.listPower reference finite 0)
        (Measure.SFinite.listPower finite 0))) :
    KernelInvariant
      (Measure.add (Measure.smul half (Measure.listPower reference finite 1))
        (Measure.smul half (Measure.listPower reference finite 2)))
      (splitMergeKernel births.kernel births.finite (patchBirth element) stageOneDensity
        births.density (fun _ => Dedekind.one) stageOneDensity_measurable births.measurable
        (MeasurableMap.constant _ borel Dedekind.one)) :=
  splitMergeKernel_invariant (selectionDensityMeasurable := births.measurable)
    (factorMeasurable := MeasurableMap.constant _ borel Dedekind.one)
    (positionCountingFinite.prod (Measure.SFinite.listPower finite 1))
    (positionCountingFinite.prod (Measure.SFinite.listPower finite 0))
    _ (stageOneDensity_represents reference finite) stageOneDensity_nonnegative births.markov
    births.represents births.nonnegative
    (patchBirth_reference_change reference finite) (fun _ _ => Dedekind.one_positive)

end StageOne

end
end Problib.Inference
