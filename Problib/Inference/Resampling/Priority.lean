module

public import Problib.Inference.Resampling.Ancestors

set_option autoImplicit false

/-! # Priority resampling

Priority resampling draws parents from priorities `p` rather than from weights.
A priority is a measurable function of a lane's value and weight. Child `k`
takes its parent `a`'s value at the weight `(w_a / p_a) · P/N`, where
`P = Σ p` and `N` is the input lane count. When `p = w` this is the mean
weight, and the step is plain resampling.

The step is plain resampling on a lifted population (`priorityResample`). Each
lane `(x, w)` is lifted to the value `(x, w/p)` at weight `p = p(x, w)`
(`priorityLift`). Resampling then gives every child a lifted parent at the mean
priority `P/N`, and each child `((x, r), m)` is lowered to `x` at `r · m`
(`priorityLower`). Any ancestor kernel whose offspring counts are unbiased for
the priorities serves: multinomial, systematic or stratified, read on the lifted
population.

The step keeps every population's empirical measure exactly when a zero priority
implies a zero weight (`priority_resample_invariant`). Resampling keeps the lifted
empirical measure `(1/N) Σ p_i δ_(x_i, w_i/p_i)`, and lowering reads it
against the carried ratio, which gives `(1/N) Σ w_i δ_(x_i)` wherever
`p_i ≠ 0`.

The condition is also necessary (`priority_resample_invariant_iff`). A lane
with `w > 0` and `p = 0` is never drawn, and its mass is lost: the step's
expected empirical measure is the input's with every lane read at weight
`p · (w/p)`, which is zero at such a lane (`priority_resample_mean`). Two lanes
of weight `1` at priorities `1` and `0` give an output of expected total mass
`1/2`, while the input has total mass `1`.

At `P = 0` the lifted population has total weight zero, so the ancestor kernel's
zero-weight policy applies. Every child takes its declared parent at weight `0`
(`priority_zero_total`). Under the condition every input weight is then zero as
well.

GenParticleFilters.jl instead rescales the weights to sum to the particle count.
That makes the evidence estimate a ratio estimator. Here the child weight uses
the priority total `P` exactly, and no rescaling by the output weights occurs.
-/

namespace Problib.Inference

open Problib.Measure Problib.Real

variable {α : Type} {space : Space α}

public section

/-! ### Lifting and lowering -/

/-- Apply one map to every lane. -/
@[expose] def populationMap {ι β γ : Type} (map : β → γ) (draws : ι → β) : ι → γ :=
  fun lane => map (draws lane)

theorem populationMap_measurable {ι β γ : Type} {source : Space β} {target : Space γ}
    {map : β → γ} (measurable : MeasurableMap source target map) :
    MeasurableMap (Space.pi fun _ : ι => source) (Space.pi fun _ : ι => target)
      (populationMap map) :=
  Space.pi_measurable fun lane =>
    MeasurableMap.comp measurable (Space.coordinate_measurable (fun _ : ι => source) lane)

/-- Lift a lane `(x, w)` to the value `(x, w/p)` at weight `p = p(x, w)`. -/
@[expose] noncomputable def priorityLift (priority : α × NNReal → NNReal)
    (lane : α × NNReal) : (α × NNReal) × NNReal :=
  ((lane.1, NNReal.div lane.2 (priority lane)), priority lane)

/-- Lower a resampled lane `((x, r), m)` to `x` at weight `r · m`. -/
@[expose] noncomputable def priorityLower (lane : (α × NNReal) × NNReal) : α × NNReal :=
  (lane.1.1, NNReal.mul lane.1.2 lane.2)

variable {priority : α × NNReal → NNReal}

theorem priorityLift_measurable
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority) :
    MeasurableMap (Space.product space weightSpace)
      (Space.product (Space.product space weightSpace) weightSpace) (priorityLift priority) :=
  Space.pair_measurable
    (Space.pair_measurable (Space.first_measurable space weightSpace)
      (weight_div_measurable (Space.second_measurable space weightSpace) priorityMeasurable))
    priorityMeasurable

theorem priorityLower_measurable :
    MeasurableMap (Space.product (Space.product space weightSpace) weightSpace)
      (Space.product space weightSpace) (priorityLower (α := α)) :=
  Space.pair_measurable
    (MeasurableMap.comp (Space.first_measurable space weightSpace)
      (Space.first_measurable _ weightSpace))
    (weight_mul_measurable
      (MeasurableMap.comp (Space.second_measurable space weightSpace)
        (Space.first_measurable _ weightSpace))
      (Space.second_measurable _ weightSpace))

/-! ### The step -/

/-- Lift every lane, resample the lifted population, and lower every child. -/
@[expose] noncomputable def priorityResample {ι κ : Type} (inLanes : Lanes ι)
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority)
    (ancestors :
      Kernel (populationSpace ι (Space.product space weightSpace)) (ancestorSpace ι κ))
    (ancestorsFinite : Kernel.IsSFinite ancestors) :
    Kernel (populationSpace ι space) (populationSpace κ space) :=
  ((resample inLanes ancestors ancestorsFinite).precomp (populationMap (priorityLift priority))
      (populationMap_measurable (priorityLift_measurable priorityMeasurable))).map
    (populationMap priorityLower)
    (populationMap_measurable priorityLower_measurable)

/-- The step as three population steps: lift, resample, lower. -/
theorem priorityResample_eq_comp {ι κ : Type} (inLanes : Lanes ι)
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority)
    (ancestors :
      Kernel (populationSpace ι (Space.product space weightSpace)) (ancestorSpace ι κ))
    (ancestorsFinite : Kernel.IsSFinite ancestors) :
    (Kernel.deterministic (populationMap (priorityLift priority))
        (populationMap_measurable (ι := ι) (priorityLift_measurable priorityMeasurable))).comp
      ((resample inLanes ancestors ancestorsFinite).comp
        (Kernel.deterministic (populationMap priorityLower)
          (populationMap_measurable (ι := κ) priorityLower_measurable))) =
      priorityResample inLanes priorityMeasurable ancestors ancestorsFinite := by
  rw [Kernel.comp_deterministic]
  apply Kernel.ext
  intro draws
  rw [Kernel.deterministic_comp_apply]
  rfl

/-- The lifted population's total weight is the priority total `P`. -/
theorem lifted_totalWeight {ι : Type} (inLanes : Lanes ι) (draws : ι → α × NNReal) :
    totalWeight inLanes (populationMap (priorityLift priority) draws) =
      NNReal.additiveLaws.listSum (inLanes.list.map fun lane => priority (draws lane)) :=
  rfl

/-- Every child is a probability when the ancestors are. -/
theorem priority_markov {ι κ : Type} (inLanes : Lanes ι)
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority)
    {ancestors :
      Kernel (populationSpace ι (Space.product space weightSpace)) (ancestorSpace ι κ)}
    {ancestorsFinite : Kernel.IsSFinite ancestors}
    (markov : ∀ draws, Measure.IsProbability (ancestors draws)) (draws : ι → α × NNReal) :
    Measure.IsProbability
      (priorityResample inLanes priorityMeasurable ancestors ancestorsFinite draws) := by
  unfold priorityResample
  rw [Kernel.map_apply _ _ (populationMap_measurable priorityLower_measurable),
    Kernel.precomp_apply _ _
    (populationMap_measurable (priorityLift_measurable priorityMeasurable)), resample_apply]
  exact ((markov _).map _ _).map _ _

/-- At priority total zero, every child takes its declared parent at weight
zero. -/
theorem priority_zero_total {ι κ : Type} {inLanes : Lanes ι}
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority)
    {ancestors :
      Kernel (populationSpace ι (Space.product space weightSpace)) (ancestorSpace ι κ)}
    {ancestorsFinite : Kernel.IsSFinite ancestors} {parents : κ → ι}
    (policy : ZeroWeightPolicy inLanes ancestors parents) {draws : ι → α × NNReal}
    (zero : totalWeight inLanes (populationMap (priorityLift priority) draws) = NNReal.zero) :
    priorityResample inLanes priorityMeasurable ancestors ancestorsFinite draws =
      Measure.dirac _ (fun child => ((draws (parents child)).1, NNReal.zero)) := by
  unfold priorityResample
  rw [Kernel.map_apply _ _ (populationMap_measurable priorityLower_measurable),
    Kernel.precomp_apply _ _
      (populationMap_measurable (priorityLift_measurable priorityMeasurable)),
    resample_zero_weight policy zero, Measure.map_dirac]
  congr 1
  funext child
  exact Prod.ext rfl (NNReal.mul_zero _)

/-! ### Invariance -/

/-- A lifted value `(x, r)` read against its ratio `r`. -/
private theorem reweighed_measurable {function : α → ENNReal}
    (measurable : ENNRealMeasurable space function) :
    ENNRealMeasurable (Space.product space weightSpace) (fun lane =>
      ENNReal.mul (ENNReal.finite lane.2) (function lane.1)) :=
  ENNRealMeasurable.mul
    (finite_weight_measurable (Space.second_measurable space weightSpace))
    (ENNRealMeasurable.comp measurable (Space.first_measurable space weightSpace))

private theorem mul_left_comm (first second third : ENNReal) :
    ENNReal.mul first (ENNReal.mul second third) =
      ENNReal.mul second (ENNReal.mul first third) := by
  rw [← ENNReal.mul_assoc, ENNReal.mul_comm first second, ENNReal.mul_assoc]

/-- A lane read through its priority: `(x, p · (w/p))`. Its weight is `w` where
`p ≠ 0` and zero where `p = 0`. -/
@[expose] noncomputable def priorityKept (priority : α × NNReal → NNReal)
    (lane : α × NNReal) : α × NNReal :=
  (lane.1, NNReal.mul (priority lane) (NNReal.div lane.2 (priority lane)))

theorem priorityKept_measurable
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority) :
    MeasurableMap (Space.product space weightSpace) (Space.product space weightSpace)
      (priorityKept priority) :=
  Space.pair_measurable (Space.first_measurable space weightSpace)
    (weight_mul_measurable priorityMeasurable
      (weight_div_measurable (Space.second_measurable space weightSpace) priorityMeasurable))

/-- Where a zero priority implies a zero weight, reading a lane through its
priority keeps it. -/
theorem priorityKept_eq (positive : ∀ lane, priority lane = NNReal.zero → lane.2 = NNReal.zero)
    (lane : α × NNReal) : priorityKept priority lane = lane := by
  refine Prod.ext rfl ?_
  show NNReal.mul (priority lane) (NNReal.div lane.2 (priority lane)) = lane.2
  by_cases zero : priority lane = NNReal.zero
  · rw [zero, positive lane zero, NNReal.zero_mul]
  · exact NNReal.mul_div_cancel _ zero

/-- Priority resampling's expected empirical measure is the input population's,
with every lane read through its priority. A lane of zero priority is never
drawn, so its mass is dropped. -/
theorem priority_resample_mean {ι κ : Type} {inLanes : Lanes ι} {outLanes : Lanes κ}
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority)
    {ancestors :
      Kernel (populationSpace ι (Space.product space weightSpace)) (ancestorSpace ι κ)}
    {ancestorsFinite : Kernel.IsSFinite ancestors}
    (unbiased : OffspringUnbiased inLanes outLanes ancestors) :
    (priorityResample inLanes priorityMeasurable ancestors ancestorsFinite).comp
        (empirical outLanes space) =
      (empirical inLanes space).precomp (populationMap (priorityKept priority))
        (populationMap_measurable (priorityKept_measurable priorityMeasurable)) := by
  apply Kernel.ext
  intro draws
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  let reweighed : α × NNReal → ENNReal := fun lane =>
    ENNReal.mul (ENNReal.finite lane.2) (function lane.1)
  have reweighedMeasurable := reweighed_measurable measurable
  -- Lowering a lifted population reads its empirical measure against the ratio.
  have lowered : ∀ lifted : κ → (α × NNReal) × NNReal,
      lintegral (empirical outLanes space (populationMap priorityLower lifted))
          function =
        lintegral (empirical outLanes (Space.product space weightSpace) lifted) reweighed := by
    intro lifted
    rw [lintegral_empirical _ _ measurable, lintegral_empirical _ _ reweighedMeasurable]
    refine congrArg (ENNReal.mul _) (congrArg ENNReal.additiveLaws.listSum
      (List.map_congr_left fun child _ => ?_))
    show ENNReal.mul (ENNReal.finite (NNReal.mul (lifted child).1.2 (lifted child).2))
        (function (lifted child).1.1) =
      ENNReal.mul (ENNReal.finite (lifted child).2)
        (ENNReal.mul (ENNReal.finite (lifted child).1.2) (function (lifted child).1.1))
    rw [← ENNReal.finite_mul_finite, ENNReal.mul_assoc, mul_left_comm]
  have resampled : lintegral ((resample inLanes ancestors ancestorsFinite).comp
        (empirical outLanes (Space.product space weightSpace))
        (populationMap (priorityLift priority) draws)) reweighed =
      lintegral (empirical inLanes (Space.product space weightSpace)
        (populationMap (priorityLift priority) draws)) reweighed := by
    rw [empirical_resample unbiased]
  rw [Kernel.lintegral_comp _ _ _ reweighedMeasurable] at resampled
  unfold priorityResample
  rw [Kernel.lintegral_comp _ _ _ measurable,
    Kernel.map_apply _ _ (populationMap_measurable priorityLower_measurable),
    lintegral_map _ _ _ (Kernel.lintegral_measurable _ measurable), Kernel.precomp_apply _ _
      (populationMap_measurable (priorityLift_measurable priorityMeasurable))]
  refine (lintegral_congr _ lowered).trans (resampled.trans ?_)
  rw [Kernel.precomp_apply, lintegral_empirical _ _ reweighedMeasurable,
    lintegral_empirical _ _ measurable]
  refine congrArg (ENNReal.mul _) (congrArg ENNReal.additiveLaws.listSum
    (List.map_congr_left fun lane _ => ?_))
  show ENNReal.mul (ENNReal.finite (priority (draws lane)))
      (ENNReal.mul (ENNReal.finite (NNReal.div (draws lane).2 (priority (draws lane))))
        (function (draws lane).1)) =
    ENNReal.mul (ENNReal.finite (NNReal.mul (priority (draws lane))
      (NNReal.div (draws lane).2 (priority (draws lane))))) (function (draws lane).1)
  rw [← ENNReal.mul_assoc, ENNReal.finite_mul_finite]

/-- Priority resampling keeps every population's empirical measure when a zero
priority implies a zero weight. -/
theorem priority_resample_invariant {ι κ : Type} {inLanes : Lanes ι} {outLanes : Lanes κ}
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority)
    (positive : ∀ lane, priority lane = NNReal.zero → lane.2 = NNReal.zero)
    {ancestors :
      Kernel (populationSpace ι (Space.product space weightSpace)) (ancestorSpace ι κ)}
    {ancestorsFinite : Kernel.IsSFinite ancestors}
    (unbiased : OffspringUnbiased inLanes outLanes ancestors) :
    ResampleInvariant inLanes outLanes
      (priorityResample inLanes priorityMeasurable ancestors ancestorsFinite) := by
  refine (priority_resample_mean priorityMeasurable unbiased).trans (Kernel.ext fun draws => ?_)
  rw [Kernel.precomp_apply]
  have kept : populationMap (priorityKept priority) draws = draws :=
    funext fun lane => priorityKept_eq positive (draws lane)
  rw [kept]

/-- The condition is necessary. A lane of positive weight and zero priority is
never drawn, so a population of copies of it loses all its mass: its
empirical measure has mass `w`, and the step's expected one has mass zero. -/
theorem priority_resample_invariant_iff {ι κ : Type} {inLanes : Lanes ι} {outLanes : Lanes κ}
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority)
    {ancestors :
      Kernel (populationSpace ι (Space.product space weightSpace)) (ancestorSpace ι κ)}
    {ancestorsFinite : Kernel.IsSFinite ancestors}
    (unbiased : OffspringUnbiased inLanes outLanes ancestors) :
    ResampleInvariant inLanes outLanes
        (priorityResample inLanes priorityMeasurable ancestors ancestorsFinite) ↔
      ∀ lane, priority lane = NNReal.zero → lane.2 = NNReal.zero := by
  refine ⟨fun invariant lane zero => ?_,
    fun positive => priority_resample_invariant priorityMeasurable positive unbiased⟩
  have masses := congrArg (fun kernel : Kernel (populationSpace ι space) space =>
      lintegral (kernel fun _ => lane) fun _ => ENNReal.one)
    ((priority_resample_mean priorityMeasurable unbiased).symm.trans invariant)
  change lintegral (((empirical inLanes space).precomp _ _) fun _ => lane) (fun _ => ENNReal.one) =
    lintegral (empirical inLanes space fun _ => lane) (fun _ => ENNReal.one) at masses
  rw [Kernel.precomp_apply, lintegral_empirical _ _ (ENNRealMeasurable.constant _ _),
    lintegral_empirical _ _ (ENNRealMeasurable.constant _ _)] at masses
  change ENNReal.mul (ENNReal.finite inLanes.share) (ENNReal.additiveLaws.listSum
      (inLanes.list.map fun _ => ENNReal.mul (ENNReal.finite (NNReal.mul (priority lane)
        (NNReal.div lane.2 (priority lane)))) ENNReal.one)) =
    ENNReal.mul (ENNReal.finite inLanes.share) (ENNReal.additiveLaws.listSum
      (inLanes.list.map fun _ => ENNReal.mul (ENNReal.finite lane.2) ENNReal.one)) at masses
  rw [Lanes.average_const, Lanes.average_const] at masses
  rw [zero, NNReal.zero_mul, ENNReal.mul_one, ENNReal.mul_one] at masses
  exact (ENNReal.finite.inj masses).symm

/-! ### Multinomial priorities -/

/-- Children draw their parents independently from `categorical p`: multinomial
resampling of the lifted population. -/
theorem multinomial_priority_invariant {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count]
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority)
    (positive : ∀ lane, priority lane = NNReal.zero → lane.2 = NNReal.zero) :
    ResampleInvariant inLanes (Lanes.fin count)
      (priorityResample inLanes priorityMeasurable
        (multinomialAncestors inLanes count (Space.product space weightSpace))
        (multinomialFinite inLanes count (Space.product space weightSpace))) :=
  priority_resample_invariant priorityMeasurable positive
    (multinomial_offspring_unbiased inLanes count)

/-- Every target is invariant under multinomial priority resampling. -/
theorem multinomial_priority_step_invariant {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count]
    (priorityMeasurable : MeasurableMap (Space.product space weightSpace) weightSpace priority)
    (positive : ∀ lane, priority lane = NNReal.zero → lane.2 = NNReal.zero)
    (target : Measure space) :
    StepInvariant inLanes (Lanes.fin count) target target
      (priorityResample inLanes priorityMeasurable
        (multinomialAncestors inLanes count (Space.product space weightSpace))
        (multinomialFinite inLanes count (Space.product space weightSpace))) :=
  step_invariant_of_resample
    (priority_markov inLanes priorityMeasurable
      (multinomial_markov inLanes count (Space.product space weightSpace)))
    (multinomial_priority_invariant inLanes count priorityMeasurable positive)

end

end Problib.Inference
