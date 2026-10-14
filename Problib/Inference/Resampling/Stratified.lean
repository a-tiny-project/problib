module

public import Problib.Inference.Resampling.Ancestors
import Problib.Measure.Uniform

set_option autoImplicit false

/-! # Stratified ancestors

Stratified resampling gives every child its own uniform. The child at position
`k` of `M` reads the categorical index at `(k + u_k)/M`, and the children's
uniforms are independent (`stratifiedAncestors`). At total weight zero the
parents are `zeroParents`, as for systematic and multinomial resampling
(`stratified_zero_weight`).

Child `k`'s parent law is systematic resampling's child `k`
(`stratifiedLane_eq`): each reads the point `(k + u)/M` of one uniform, and
only the joint law differs. The offspring equation reads per-child marginals
alone, so stratified resampling inherits `systematic_offspring_unbiased`
(`stratified_offspring_unbiased`). A child's marginal is not `categorical w`,
so `offspring_unbiased_of_marginals` does not apply. Under the equation,
resampling keeps every population's empirical measure
(`stratified_resample_invariant`).
-/

namespace Problib.Inference

open Problib.Measure Problib.Real
open Problib.Measure.Real (UnitInterval unitBorel uniform01 uniform01_isProbability)

variable {α : Type} {space : Space α}

public section

/-- Child `child`'s parent from its own uniform `u`, at the point
`(child + u)/M`. At zero total weight, `zeroParents`. -/
@[expose] noncomputable def stratifiedLane {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] (space : Space α) (child : Fin count) :
    Kernel (populationSpace ι space) (Space.discrete ι) :=
  Kernel.piecewise (zeroTotal inLanes) (zeroTotal_measurable inLanes space)
    (Kernel.const _ (Measure.dirac _ (zeroParents inLanes (Lanes.fin count) child)))
    (((Kernel.const (populationSpace ι space) uniform01).attach
        (Kernel.IsSFinite.ofMarkov fun _ => uniform01_isProbability)).map
      (fun pair => systematicParents inLanes (Lanes.fin count) pair.1 pair.2 child)
      (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin count => Space.discrete ι)
        child) (systematicParents_measurable inLanes (Lanes.fin count))))

/-- A child's parent law is systematic resampling's for that child. -/
theorem stratifiedLane_eq {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (space : Space α) (child : Fin count) :
    stratifiedLane inLanes count space child =
      (systematicAncestors inLanes (Lanes.fin count) space).map (fun parents => parents child)
        (Space.coordinate_measurable (fun _ : Fin count => Space.discrete ι) child) := by
  apply Kernel.ext
  intro draws
  rw [Kernel.map_apply]
  unfold stratifiedLane systematicAncestors
  by_cases zero : zeroTotal inLanes draws
  · rw [Kernel.piecewise_apply_of_mem _ _ _ _ draws zero,
      Kernel.piecewise_apply_of_mem _ _ _ _ draws zero, Kernel.const_apply, Kernel.const_apply,
      Measure.map_dirac]
  · rw [Kernel.piecewise_apply_of_not_mem _ _ _ _ draws zero,
      Kernel.piecewise_apply_of_not_mem _ _ _ _ draws zero, Kernel.map_apply, Kernel.map_apply,
      Measure.map_comp]

/-- Each child's parent is a probability. -/
theorem stratifiedLane_markov {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (space : Space α) (child : Fin count) (draws : ι → α × NNReal) :
    Measure.IsProbability (stratifiedLane inLanes count space child draws) := by
  unfold stratifiedLane
  by_cases zero : zeroTotal inLanes draws
  · rw [Kernel.piecewise_apply_of_mem _ _ _ _ draws zero]
    exact Measure.IsProbability.dirac _ _
  · rw [Kernel.piecewise_apply_of_not_mem _ _ _ _ draws zero]
    exact (Measure.IsProbability.map uniform01_isProbability _
      (Kernel.pair_left_measurable (source := populationSpace ι space) draws)).map _
      (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin count => Space.discrete ι)
        child) (systematicParents_measurable inLanes (Lanes.fin count)))

noncomputable def stratifiedLaneFinite {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] (space : Space α) (child : Fin count) :
    Kernel.IsSFinite (stratifiedLane inLanes count space child) :=
  Kernel.IsSFinite.ofMarkov (stratifiedLane_markov inLanes count space child)

/-- Every child's parent, from independent uniforms. -/
@[expose] noncomputable def stratifiedAncestors {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] (space : Space α) :
    Kernel (populationSpace ι space) (ancestorSpace ι (Fin count)) :=
  Kernel.finProduct count (stratifiedLane inLanes count space)
    (stratifiedLaneFinite inLanes count space)

/-- The children's parents form a probability at every population. -/
theorem stratified_markov {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (space : Space α) (draws : ι → α × NNReal) :
    Measure.IsProbability (stratifiedAncestors inLanes count space draws) :=
  Kernel.finProduct_markov count _ _ (stratifiedLane_markov inLanes count space) draws

noncomputable def stratifiedFinite {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] (space : Space α) :
    Kernel.IsSFinite (stratifiedAncestors inLanes count space) :=
  Kernel.IsSFinite.ofMarkov (stratified_markov inLanes count space)

theorem stratified_zero_weight {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count] :
    ZeroWeightPolicy inLanes (stratifiedAncestors inLanes count space)
      (zeroParents inLanes (Lanes.fin count)) := fun draws zero =>
  Kernel.finProduct_dirac count _ _ fun _ =>
    Kernel.piecewise_apply_of_mem _ _ _ _ draws ((zeroTotal_iff inLanes draws).mpr zero)

/-- Every child's parent law is its lane's. -/
theorem stratified_marginal {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (draws : ι → α × NNReal) (child : Fin count) :
    (stratifiedAncestors inLanes count space draws).map (fun parents => parents child)
        (Space.coordinate_measurable (fun _ : Fin count => Space.discrete ι) child) =
      stratifiedLane inLanes count space child draws := by
  apply Measure.ext
  intro region measurable
  have indicatorMeasurable : ENNRealMeasurable (Space.discrete ι)
      (ennrealIndicator region fun _ => ENNReal.one) :=
    ENNRealMeasurable.indicator measurable (ENNRealMeasurable.constant _ ENNReal.one)
  rw [apply_eq_lintegral_indicator ((stratifiedAncestors inLanes count space draws).map _ _)
      measurable,
    lintegral_map _ _ _ indicatorMeasurable,
    apply_eq_lintegral_indicator (stratifiedLane inLanes count space child draws) measurable]
  exact Kernel.lintegral_finProduct_coordinate count _ _
    (stratifiedLane_markov inLanes count space) child draws _ indicatorMeasurable

/-- Stratified resampling's offspring counts are unbiased: every child's parent
law is systematic resampling's, and the equation reads only those laws. -/
theorem stratified_offspring_unbiased {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] :
    OffspringUnbiased inLanes (Lanes.fin count) (stratifiedAncestors inLanes count space) := by
  intro draws index
  have each : ∀ child : Fin count,
      stratifiedAncestors inLanes count space draws (fun parents => parents child = index) =
        systematicAncestors inLanes (Lanes.fin count) space draws
          (fun parents => parents child = index) := by
    intro child
    have single := Space.discrete_measurable (α := ι) fun lane : ι => lane = index
    have read := congrArg (fun measure : Measure (Space.discrete ι) =>
      measure (fun lane : ι => lane = index))
      ((stratified_marginal inLanes count draws child).trans
        (congrArg (fun kernel => kernel draws) (stratifiedLane_eq inLanes count space child)))
    simp only [Kernel.map_apply] at read
    rw [Measure.map_apply _ _ _ single, Measure.map_apply _ _ _ single] at read
    exact read
  simp only [each]
  exact systematic_offspring_unbiased inLanes (Lanes.fin count) draws index

/-- Stratified resampling keeps every population's empirical measure. -/
theorem stratified_resample_invariant {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] :
    ResampleInvariant inLanes (Lanes.fin count)
      (resample inLanes (stratifiedAncestors inLanes count space)
        (stratifiedFinite inLanes count space)) :=
  empirical_resample (stratified_offspring_unbiased inLanes count)

/-- Every target is invariant under stratified resampling. -/
theorem stratified_step_invariant {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (target : Measure space) :
    StepInvariant inLanes (Lanes.fin count) target target
      (resample inLanes (stratifiedAncestors inLanes count space)
        (stratifiedFinite inLanes count space)) := by
  refine step_invariant_of_resample (fun draws => ?_) (stratified_resample_invariant inLanes count)
  rw [resample_apply]
  exact (stratified_markov inLanes count space draws).map _ _

end

end Problib.Inference
