module

public import Problib.Inference.Weighting
public import Problib.Inference.Invariance
public import Problib.Measure.Pi
public import Problib.FiniteEnumeration
public import Problib.Measure.Integral.Lebesgue.Measure
set_option autoImplicit false

/-! Populations of weighted draws.

A population holds one weighted draw per lane. Its empirical measure
`(1/N) Σ_j w_j δ_{x_j}` is the barycenter of a uniformly picked lane
(`empirical`, `pick`). A law of populations is invariant for a target when its
expected empirical measure is the target (`EmpiricalInvariant`). That says
exactly that a picked lane is calibrated for the target
(`empirical_invariant_iff_calibrated`), so every statement about calibrated
draws reads on populations. The lanes may depend on each other. Every mean
identity here reads one lane's marginal at a time, and none needs a product
measure.

A population step is invariant from one target to another when it carries
every law invariant for the first to a law invariant for the second
(`StepInvariant`). Invariant steps compose (`step_invariant_comp`), and a step
chosen by a schedule drawn independently of the population is invariant when
every scheduled step is (`step_invariant_mixture`). A step whose lanes each
continue by one weighted kernel moves the empirical measure by the kernel's
barycenters (`intertwines_of_lanes`), so propagation and rejuvenation are
invariant steps (`empirical_propagate`, `empirical_rejuvenate`). Replicated
calibrated lanes form an invariant population (`empirical_replicate`), and
mapping every lane's value maps the target (`empirical_map`). The mean weight
and the weighted average of a real integrand are unbiased for the target's
mass and integral (`empirical_mass_unbiased`, `empirical_estimate_unbiased`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Measure.Real (Carrier)
open Problib.Measure.SimpleFunction (finiteSum)
open Problib.Real.Construction

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

public section

/-! ### Lanes -/

/-- The lanes of a population: an enumeration of a finite, nonempty index. -/
structure Lanes (ι : Type) : Type where
  list : List ι
  enumeration : FiniteEnumeration list
  nonempty : list ≠ []

namespace Lanes

variable {ι : Type}

/-- The number of lanes. -/
abbrev count (lanes : Lanes ι) : Nat := lanes.list.length

theorem count_pos (lanes : Lanes ι) : 0 < lanes.count :=
  List.length_pos_iff.mpr lanes.nonempty

/-- The lanes `0, …, count - 1` of a nonzero count. -/
@[expose] def fin (count : Nat) [NeZero count] : Lanes (Fin count) where
  list := List.finRange count
  enumeration := FiniteEnumeration.finRange count
  nonempty := List.ne_nil_of_length_pos (by
    rw [List.length_finRange]
    exact Nat.pos_of_neZero count)

/-- Each lane's share of the population, `1/N`. -/
@[expose] noncomputable def share (lanes : Lanes ι) : NNReal :=
  NNReal.ofRat ((lanes.count : Rat)⁻¹)
    (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr lanes.count_pos)))

private theorem ofRat_congr {left right : Rat} (equal : left = right)
    {leftNonnegative : 0 ≤ left} {rightNonnegative : 0 ≤ right} :
    NNReal.ofRat left leftNonnegative = NNReal.ofRat right rightNonnegative := by
  subst equal
  rfl

/-- The lanes' shares make one: `(1/N) · N = 1`. -/
theorem share_mul_count (lanes : Lanes ι) :
    NNReal.mul lanes.share (NNReal.ofRat (lanes.count : Rat) Rat.natCast_nonneg) =
      NNReal.one := by
  have nonzero : (lanes.count : Rat) ≠ 0 := fun zero =>
    Nat.pos_iff_ne_zero.mp lanes.count_pos (Rat.natCast_eq_zero_iff.mp zero)
  rw [share, ← NNReal.ofRat_mul]
  exact (ofRat_congr (Rat.inv_mul_cancel _ nonzero)).trans NNReal.ofRat_one

/-- Averaging one value over the lanes returns it. -/
theorem average_const (lanes : Lanes ι) (value : ENNReal) :
    ENNReal.mul (ENNReal.finite lanes.share) (finiteSum (lanes.list.map fun _ => value)) =
      value := by
  rw [finiteSum_map_const, ← ENNReal.mul_assoc, ENNReal.ofRat, ENNReal.finite_mul_finite,
    lanes.share_mul_count]
  exact ENNReal.one_mul value

/-- The sum of nonnegative values over the lanes. -/
@[expose] noncomputable def sum (lanes : Lanes ι) (values : ι → NNReal) : NNReal :=
  lanes.list.foldr (fun lane total => NNReal.add (values lane) total) NNReal.zero

/-- The average of nonnegative values over the lanes. -/
@[expose] noncomputable def average (lanes : Lanes ι) (values : ι → NNReal) : NNReal :=
  NNReal.mul lanes.share (lanes.sum values)

/-- The sum of real values over the lanes. -/
@[expose] noncomputable def realSum (lanes : Lanes ι) (values : ι → Carrier) : Carrier :=
  lanes.list.foldr (fun lane total => Dedekind.add (values lane) total) Dedekind.zero

/-- The average of real values over the lanes. -/
@[expose] noncomputable def realAverage (lanes : Lanes ι) (values : ι → Carrier) : Carrier :=
  Dedekind.mul lanes.share.toReal (lanes.realSum values)

private theorem foldr_finite (values : ι → NNReal) (list : List ι) :
    ENNReal.finite (list.foldr (fun lane total => NNReal.add (values lane) total) NNReal.zero) =
      finiteSum (list.map fun lane => ENNReal.finite (values lane)) := by
  induction list with
  | nil => rfl
  | cons lane list induction =>
      show ENNReal.add (ENNReal.finite (values lane))
          (ENNReal.finite (list.foldr (fun lane total => NNReal.add (values lane) total)
            NNReal.zero)) =
        ENNReal.add (ENNReal.finite (values lane))
          (finiteSum (list.map fun lane => ENNReal.finite (values lane)))
      rw [induction]

private theorem foldr_toReal (values : ι → NNReal) (list : List ι) :
    (list.foldr (fun lane total => NNReal.add (values lane) total) NNReal.zero).toReal =
      list.foldr (fun lane total => Dedekind.add (values lane).toReal total) Dedekind.zero := by
  induction list with
  | nil => rfl
  | cons lane list induction =>
      show Dedekind.add (values lane).toReal
          (list.foldr (fun lane total => NNReal.add (values lane) total) NNReal.zero).toReal = _
      rw [induction]
      rfl

private theorem foldr_sub (left right : ι → Carrier) (list : List ι) :
    list.foldr (fun lane total => Dedekind.add (Dedekind.sub (left lane) (right lane)) total)
        Dedekind.zero =
      Dedekind.sub (list.foldr (fun lane total => Dedekind.add (left lane) total) Dedekind.zero)
        (list.foldr (fun lane total => Dedekind.add (right lane) total) Dedekind.zero) := by
  induction list with
  | nil => exact (Dedekind.sub_self Dedekind.zero).symm
  | cons lane list induction =>
      show Dedekind.add (Dedekind.sub (left lane) (right lane))
          (list.foldr (fun lane total => Dedekind.add (Dedekind.sub (left lane) (right lane)) total)
            Dedekind.zero) =
        Dedekind.sub
          (Dedekind.add (left lane)
            (list.foldr (fun lane total => Dedekind.add (left lane) total) Dedekind.zero))
          (Dedekind.add (right lane)
            (list.foldr (fun lane total => Dedekind.add (right lane) total) Dedekind.zero))
      rw [induction]
      simp only [Dedekind.sub_eq_add_neg, Dedekind.neg_add]
      rw [Dedekind.add_assoc (left lane), Dedekind.add_left_comm (Dedekind.neg (right lane)),
        ← Dedekind.add_assoc (left lane)]

/-- A nonnegative sum over the lanes, read into the extended reals. -/
theorem finite_sum (lanes : Lanes ι) (values : ι → NNReal) :
    ENNReal.finite (lanes.sum values) =
      finiteSum (lanes.list.map fun lane => ENNReal.finite (values lane)) :=
  foldr_finite values lanes.list

/-- A nonnegative average over the lanes, read into the extended reals. -/
theorem finite_average (lanes : Lanes ι) (values : ι → NNReal) :
    ENNReal.finite (lanes.average values) =
      ENNReal.mul (ENNReal.finite lanes.share)
        (finiteSum (lanes.list.map fun lane => ENNReal.finite (values lane))) := by
  rw [average, ← ENNReal.finite_mul_finite, finite_sum]

/-- A nonnegative average over the lanes, read as a real number. -/
theorem toReal_average (lanes : Lanes ι) (values : ι → NNReal) :
    (lanes.average values).toReal = lanes.realAverage fun lane => (values lane).toReal := by
  show Dedekind.mul lanes.share.toReal (lanes.sum values).toReal = _
  rw [sum, foldr_toReal]
  rfl

/-- Real averages over the lanes subtract. -/
theorem realAverage_sub (lanes : Lanes ι) (left right : ι → Carrier) :
    lanes.realAverage (fun lane => Dedekind.sub (left lane) (right lane)) =
      Dedekind.sub (lanes.realAverage left) (lanes.realAverage right) := by
  unfold realAverage realSum
  rw [foldr_sub, Dedekind.mul_sub]

end Lanes

/-! ### Populations and their empirical measure -/

/-- Populations of weighted draws, one per lane. -/
abbrev populationSpace (ι : Type) (space : Space α) : Space (ι → α × NNReal) :=
  Space.pi fun _ : ι => Space.product space weightSpace

/-- Reading one lane of a population. -/
theorem lane_measurable {ι : Type} (space : Space α) (lane : ι) :
    MeasurableMap (populationSpace ι space) (Space.product space weightSpace)
      (fun draws => draws lane) :=
  Space.coordinate_measurable (fun _ : ι => Space.product space weightSpace) lane

/-- A uniformly picked lane of a population, with its weight,
`(1/N) Σ_j δ_{(x_j, w_j)}`. -/
@[expose] noncomputable def pick {ι : Type} (lanes : Lanes ι) (space : Space α) :
    Kernel (populationSpace ι space) (Space.product space weightSpace) where
  toFun := fun draws => Measure.smul (ENNReal.finite lanes.share)
    (Measure.listSum (lanes.list.map fun lane => Measure.dirac _ (draws lane)))
  measurable := by
    intro set setMeasurable
    have equal : (fun draws : ι → α × NNReal => Measure.smul (ENNReal.finite lanes.share)
        (Measure.listSum (lanes.list.map fun lane =>
          Measure.dirac (Space.product space weightSpace) (draws lane))) set) =
        fun draws => ENNReal.mul (ENNReal.finite lanes.share)
          (finiteSum (lanes.list.map fun lane =>
            Kernel.deterministic (fun draws : ι → α × NNReal => draws lane)
              (lane_measurable space lane) draws set)) := by
      funext draws
      rw [Measure.smul_apply_measurable _ _ setMeasurable,
        Measure.listSum_apply _ setMeasurable, List.map_map]
      rfl
    rw [equal]
    exact (ENNRealMeasurable.finiteSum_map lanes.list fun lane =>
      (Kernel.deterministic _ (lane_measurable space lane)).measurable setMeasurable).const_mul _

theorem pick_apply {ι : Type} (lanes : Lanes ι) (space : Space α) (draws : ι → α × NNReal) :
    pick lanes space draws = Measure.smul (ENNReal.finite lanes.share)
      (Measure.listSum (lanes.list.map fun lane => Measure.dirac _ (draws lane))) :=
  rfl

/-- Integrating against a picked lane averages the integrand over the lanes. -/
theorem lintegral_pick {ι : Type} (lanes : Lanes ι) {space : Space α}
    (draws : ι → α × NNReal) {function : α × NNReal → ENNReal}
    (measurable : ENNRealMeasurable (Space.product space weightSpace) function) :
    lintegral (pick lanes space draws) function =
      ENNReal.mul (ENNReal.finite lanes.share)
        (finiteSum (lanes.list.map fun lane => function (draws lane))) := by
  rw [pick_apply, lintegral_smul_measure, lintegral_listSum, List.map_map]
  refine congrArg (ENNReal.mul _) (congrArg finiteSum (List.map_congr_left fun lane _ => ?_))
  exact lintegral_dirac _ _ measurable

/-- A picked lane is a probability. -/
theorem pick_markov {ι : Type} (lanes : Lanes ι) (space : Space α) (draws : ι → α × NNReal) :
    Measure.IsProbability (pick lanes space draws) := by
  constructor
  have total := lintegral_pick lanes draws
    (ENNRealMeasurable.constant (Space.product space weightSpace) ENNReal.one)
  rw [lintegral_const, ENNReal.one_mul, lanes.average_const] at total
  exact total

/-- The empirical measure `(1/N) Σ_j w_j δ_{x_j}` of a population, the
barycenter of a picked lane. -/
@[expose] noncomputable def empirical {ι : Type} (lanes : Lanes ι) (space : Space α) :
    Kernel (populationSpace ι space) space :=
  barycenterKernel (pick lanes space)

/-- Integrating against the empirical measure averages the weighted integrand
over the lanes. -/
theorem lintegral_empirical {ι : Type} (lanes : Lanes ι) {space : Space α}
    (draws : ι → α × NNReal) {function : α → ENNReal}
    (measurable : ENNRealMeasurable space function) :
    lintegral (empirical lanes space draws) function =
      ENNReal.mul (ENNReal.finite lanes.share)
        (finiteSum (lanes.list.map fun lane =>
          ENNReal.mul (drawWeight (draws lane)) (function (draws lane).1))) := by
  rw [empirical, barycenterKernel_apply, lintegral_barycenter _ measurable,
    lintegral_pick _ _ (weighted_integrand_measurable measurable)]

/-! ### Invariant populations -/

/-- Inv_N: the expected empirical measure of the population is the target. The
lanes may depend on each other. -/
structure EmpiricalInvariant {ι : Type} (lanes : Lanes ι) {space : Space α}
    (target : Measure space) (population : Measure (populationSpace ι space)) : Prop where
  probability : Measure.IsProbability population
  mean : population.bind (empirical lanes space) = target

/-- A measure that a Markov kernel binds into a probability is a probability. -/
private theorem isProbability_of_bind {source : Space γ} {result : Space β}
    {measure : Measure source} {kernel : Kernel source result}
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (bound : Measure.IsProbability (measure.bind kernel)) : Measure.IsProbability measure := by
  constructor
  have total := bound.univ_eq_one
  have constant : (fun input => kernel input Set.univ) = fun _ => ENNReal.one :=
    funext fun input => (markov input).univ_eq_one
  rw [Measure.bind_apply _ _ result.univ, constant, lintegral_const, ENNReal.one_mul] at total
  exact total

/-- Inv_N holds exactly when a picked lane is calibrated for the target. -/
theorem empirical_invariant_iff_calibrated {ι : Type} {lanes : Lanes ι} {space : Space α}
    {target : Measure space} {population : Measure (populationSpace ι space)} :
    EmpiricalInvariant lanes target population ↔
      Calibrated target (population.bind (pick lanes space)) := by
  constructor
  · intro invariant
    refine ⟨invariant.probability.bind _ (pick_markov lanes space), ?_⟩
    rw [barycenter_bind]
    exact invariant.mean
  · intro calibrated
    refine ⟨isProbability_of_bind (pick_markov lanes space) calibrated.probability, ?_⟩
    rw [empirical, ← barycenter_bind]
    exact calibrated.change

/-- A picked lane of an invariant population is calibrated for the target. -/
theorem pick_calibrated {ι : Type} {lanes : Lanes ι} {space : Space α}
    {target : Measure space} {population : Measure (populationSpace ι space)}
    (invariant : EmpiricalInvariant lanes target population) :
    Calibrated target (population.bind (pick lanes space)) :=
  empirical_invariant_iff_calibrated.mp invariant

/-! ### Invariant steps -/

/-- StepInv: the step carries every law of populations invariant for `source`
to one invariant for `target`. -/
@[expose] def StepInvariant {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ)
    {space : Space α} {result : Space β} (source : Measure space) (target : Measure result)
    (step : Kernel (populationSpace ι space) (populationSpace κ result)) : Prop :=
  ∀ population, EmpiricalInvariant inLanes source population →
    EmpiricalInvariant outLanes target (population.bind step)

/-- Invariant steps compose. -/
theorem step_invariant_comp {ι κ ν : Type} {first : Lanes ι} {second : Lanes κ}
    {third : Lanes ν} {space : Space α} {middle : Space β} {result : Space γ}
    {source : Measure space} {between : Measure middle} {target : Measure result}
    {firstStep : Kernel (populationSpace ι space) (populationSpace κ middle)}
    {secondStep : Kernel (populationSpace κ middle) (populationSpace ν result)}
    (firstInvariant : StepInvariant first second source between firstStep)
    (secondInvariant : StepInvariant second third between target secondStep) :
    StepInvariant first third source target (firstStep.comp secondStep) := by
  intro population invariant
  rw [← Measure.bind_assoc]
  exact secondInvariant _ (firstInvariant population invariant)

/-- Pairing an input with a fixed choice. -/
theorem choice_measurable (source : Space α) {choices : Space γ} (choice : γ) :
    MeasurableMap source (Space.product source choices) (fun input => (input, choice)) :=
  Space.pair_measurable (MeasurableMap.identity source)
    (MeasurableMap.constant source choices choice)

/-- Run the step at a choice drawn from a schedule, independently of the
input. -/
@[expose] noncomputable def mixture {source : Space α} {choices : Space γ} {target : Space β}
    (schedule : Measure choices) (scheduleFinite : Measure.SFinite schedule)
    (steps : Kernel (Space.product source choices) target) : Kernel source target :=
  ((Kernel.const source schedule).attach (Kernel.IsSFinite.const source scheduleFinite)).comp
    steps

/-- Binding a mixture integrates the bound step at each scheduled choice. -/
theorem lintegral_bind_mixture {source : Space α} {choices : Space γ} {target : Space β}
    {schedule : Measure choices} (scheduleFinite : Measure.SFinite schedule)
    {steps : Kernel (Space.product source choices) target}
    {measure : Measure source} (measureFinite : Measure.SFinite measure)
    {function : β → ENNReal} (measurable : ENNRealMeasurable target function) :
    lintegral (measure.bind (mixture schedule scheduleFinite steps)) function =
      lintegral schedule (fun choice =>
        lintegral (measure.bind (steps.precomp _ (choice_measurable source choice)))
          function) := by
  rw [mixture, ← Measure.bind_assoc, Measure.lintegral_bind _ _ measurable]
  change lintegral (Measure.prod measure schedule scheduleFinite)
    (fun pair => lintegral (steps pair) function) = _
  rw [lintegral_prod_symm _ _ measureFinite scheduleFinite
    (Kernel.lintegral_measurable steps measurable)]
  apply lintegral_congr
  intro choice
  rw [Measure.lintegral_bind _ _ measurable]
  rfl

/-- A step chosen by a schedule drawn independently of the population is
invariant when every scheduled step is. -/
theorem step_invariant_mixture {ι κ : Type} {inLanes : Lanes ι} {outLanes : Lanes κ}
    {space : Space α} {result : Space β} {source : Measure space} {target : Measure result}
    {choices : Space γ} {schedule : Measure choices}
    (probability : Measure.IsProbability schedule) (scheduleFinite : Measure.SFinite schedule)
    {steps : Kernel (Space.product (populationSpace ι space) choices) (populationSpace κ result)}
    (each : ∀ choice, StepInvariant inLanes outLanes source target
      (steps.precomp _ (choice_measurable _ choice))) :
    StepInvariant inLanes outLanes source target (mixture schedule scheduleFinite steps) := by
  intro population invariant
  have populationFinite := Measure.SFinite.ofFinite invariant.probability.to_finite
  have stepped := fun choice => each choice population invariant
  refine ⟨⟨?_⟩, (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_⟩
  · have total := lintegral_bind_mixture scheduleFinite (steps := steps) populationFinite
      (ENNRealMeasurable.constant (populationSpace κ result) ENNReal.one)
    have fibers : ∀ choice,
        lintegral (population.bind (steps.precomp _ (choice_measurable _ choice)))
          (fun _ => ENNReal.one) = ENNReal.one := by
      intro choice
      rw [lintegral_const, (stepped choice).probability.univ_eq_one, ENNReal.one_mul]
    rw [lintegral_congr _ fibers, lintegral_const, lintegral_const, probability.univ_eq_one,
      ENNReal.one_mul, ENNReal.one_mul] at total
    exact total
  · have fibers : ∀ choice,
        lintegral (population.bind (steps.precomp _ (choice_measurable _ choice)))
          (fun draws => lintegral (empirical outLanes result draws) function) =
          lintegral target function := by
      intro choice
      rw [← Measure.lintegral_bind _ _ measurable, (stepped choice).mean]
    rw [Measure.lintegral_bind _ _ measurable,
      lintegral_bind_mixture scheduleFinite populationFinite
        (Kernel.lintegral_measurable _ measurable),
      lintegral_congr _ fibers, lintegral_const, probability.univ_eq_one, ENNReal.mul_one]

/-! ### Intertwining and lane marginals -/

/-- The step moves every population's empirical measure by one kernel. -/
@[expose] def Intertwines {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ)
    {space : Space α} {result : Space β}
    (step : Kernel (populationSpace ι space) (populationSpace κ result))
    (move : Kernel space result) : Prop :=
  step.comp (empirical outLanes result) = (empirical inLanes space).comp move

/-- A Markov step that moves the empirical measure by a kernel carries
invariance for a target to invariance for the target moved by the kernel. -/
theorem step_invariant_of_intertwines {ι κ : Type} {inLanes : Lanes ι} {outLanes : Lanes κ}
    {space : Space α} {result : Space β} {source : Measure space}
    {step : Kernel (populationSpace ι space) (populationSpace κ result)}
    {move : Kernel space result}
    (markov : ∀ draws, Measure.IsProbability (step draws))
    (intertwines : Intertwines inLanes outLanes step move) :
    StepInvariant inLanes outLanes source (source.bind move) step := by
  intro population invariant
  refine ⟨invariant.probability.bind _ markov, ?_⟩
  rw [Measure.bind_assoc, intertwines, ← Measure.bind_assoc, invariant.mean]

/-- Given the population, each lane's law is the lane kernel at that lane's
draw. -/
@[expose] def LaneMarginals {ι : Type} {space : Space α} {result : Space β}
    (step : Kernel (populationSpace ι space) (populationSpace ι result))
    (lane : Kernel (Space.product space weightSpace) (Space.product result weightSpace)) :
    Prop :=
  ∀ draws index, (step draws).map (fun next => next index) (lane_measurable result index) =
    lane (draws index)

/-- A step whose lanes each continue by one reweighting kernel moves the
empirical measure by the kernel's barycenters. -/
theorem intertwines_of_lanes {ι : Type} {lanes : Lanes ι} {space : Space α}
    {result : Space β} {step : Kernel (populationSpace ι space) (populationSpace ι result)}
    {kernel : Kernel space (Space.product result weightSpace)}
    {kernelFinite : Kernel.IsSFinite kernel}
    (marginals : LaneMarginals step (reweight kernel kernelFinite)) :
    Intertwines lanes lanes step (barycenterKernel kernel) := by
  apply Kernel.ext
  intro draws
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have integrand := weighted_integrand_measurable measurable
  have lanesMeasurable : ∀ index, ENNRealMeasurable (populationSpace ι result)
      (fun next => ENNReal.mul (drawWeight (next index)) (function (next index).1)) :=
    fun index => integrand.comp (lane_measurable result index)
  rw [Kernel.lintegral_comp _ _ _ measurable, Kernel.lintegral_comp _ _ _ measurable,
    lintegral_empirical _ _ (Kernel.lintegral_measurable _ measurable),
    lintegral_congr _ fun next => lintegral_empirical lanes next measurable,
    lintegral_smul _ _ (ENNRealMeasurable.finiteSum_map lanes.list lanesMeasurable),
    lintegral_finiteSum_map _ lanes.list lanesMeasurable]
  refine congrArg (ENNReal.mul _) (congrArg finiteSum (List.map_congr_left fun index _ => ?_))
  rw [← lintegral_map _ _ (lane_measurable result index) integrand, marginals draws index,
    lintegral_reweight _ _ _ measurable]

/-- Propagation: continuing every lane by one weighted kernel and multiplying
the weights moves the target by the kernel's barycenters. -/
theorem empirical_propagate {ι : Type} {lanes : Lanes ι} {space : Space α}
    {result : Space β} {source : Measure space}
    {step : Kernel (populationSpace ι space) (populationSpace ι result)}
    {kernel : Kernel space (Space.product result weightSpace)}
    {kernelFinite : Kernel.IsSFinite kernel}
    (stepMarkov : ∀ draws, Measure.IsProbability (step draws))
    (marginals : LaneMarginals step (reweight kernel kernelFinite)) :
    StepInvariant lanes lanes source (source.bind (barycenterKernel kernel)) step :=
  step_invariant_of_intertwines stepMarkov (intertwines_of_lanes marginals)

/-! ### Rejuvenation -/

/-- Move the value by a kernel and keep the weight. -/
@[expose] noncomputable def keepWeight {space : Space α} (move : Kernel space space)
    (moveFinite : Kernel.IsSFinite move) :
    Kernel (Space.product space weightSpace) (Space.product space weightSpace) :=
  reweight (unitWeight move) (unitWeightFinite moveFinite)

/-- Moving calibrated draws by a Markov kernel that leaves the target
invariant keeps them calibrated. -/
theorem weighted_rejuvenate {space : Space α} {target : Measure space}
    {weighted : Measure (Space.product space weightSpace)} {move : Kernel space space}
    (markov : ∀ input, Measure.IsProbability (move input)) (moveFinite : Kernel.IsSFinite move)
    (invariant : KernelInvariant target move) (calibrated : Calibrated target weighted) :
    Calibrated target (weighted.bind (keepWeight move moveFinite)) := by
  have bound := weighted_bind (unitWeight_markov markov) (unitWeightFinite moveFinite)
    calibrated
  rw [barycenterKernel_unitWeight, invariant] at bound
  exact bound

/-- Rejuvenation: moving every lane by a kernel that leaves the target
invariant keeps the population invariant. -/
theorem empirical_rejuvenate {ι : Type} {lanes : Lanes ι} {space : Space α}
    {target : Measure space} {move : Kernel space space} {moveFinite : Kernel.IsSFinite move}
    {step : Kernel (populationSpace ι space) (populationSpace ι space)}
    (invariant : KernelInvariant target move)
    (stepMarkov : ∀ draws, Measure.IsProbability (step draws))
    (marginals : LaneMarginals step (keepWeight move moveFinite)) :
    StepInvariant lanes lanes target target step := by
  have propagated := empirical_propagate (lanes := lanes) (source := target) stepMarkov
    marginals
  rw [barycenterKernel_unitWeight, invariant] at propagated
  exact propagated

/-! ### Replication and mapping -/

/-- Replication: lanes that each have one calibrated law form an invariant
population, however they depend on each other. -/
theorem empirical_replicate {ι : Type} {lanes : Lanes ι} {space : Space α}
    {target : Measure space} {weighted : Measure (Space.product space weightSpace)}
    {population : Measure (populationSpace ι space)}
    (probability : Measure.IsProbability population)
    (marginals : ∀ index,
      population.map (fun draws => draws index) (lane_measurable space index) = weighted)
    (calibrated : Calibrated target weighted) : EmpiricalInvariant lanes target population := by
  refine empirical_invariant_iff_calibrated.mpr (calibrated_iff_lintegral.mpr
    ⟨probability.bind _ (pick_markov lanes space), fun function measurable => ?_⟩)
  have integrand := weighted_integrand_measurable measurable
  have lanesMeasurable : ∀ index, ENNRealMeasurable (populationSpace ι space)
      (fun draws => ENNReal.mul (drawWeight (draws index)) (function (draws index).1)) :=
    fun index => integrand.comp (lane_measurable space index)
  have each : ∀ index, lintegral population
      (fun draws => ENNReal.mul (drawWeight (draws index)) (function (draws index).1)) =
      lintegral target function := by
    intro index
    rw [← lintegral_map _ _ (lane_measurable space index) integrand, marginals index,
      calibrated.lintegral measurable]
  rw [Measure.lintegral_bind _ _ integrand,
    lintegral_congr _ fun draws => lintegral_pick lanes draws integrand,
    lintegral_smul _ _ (ENNRealMeasurable.finiteSum_map lanes.list lanesMeasurable),
    lintegral_finiteSum_map _ lanes.list lanesMeasurable]
  simp only [each]
  exact lanes.average_const _

/-- Map every lane's value and keep its weight. -/
@[expose] def lanewise {ι : Type} (map : α → β) (draws : ι → α × NNReal) : ι → β × NNReal :=
  fun index => (map (draws index).1, (draws index).2)

theorem lanewise_measurable {ι : Type} {space : Space α} {result : Space β} {map : α → β}
    (measurable : MeasurableMap space result map) :
    MeasurableMap (populationSpace ι space) (populationSpace ι result) (lanewise map) :=
  Space.pi_map fun _ => value_map_measurable measurable

/-- Mapping every lane's value maps the target. -/
theorem empirical_map {ι : Type} {lanes : Lanes ι} {space : Space α} {result : Space β}
    {target : Measure space} {population : Measure (populationSpace ι space)} {map : α → β}
    (measurable : MeasurableMap space result map)
    (invariant : EmpiricalInvariant lanes target population) :
    EmpiricalInvariant lanes (target.map map measurable)
      (population.map (lanewise map) (lanewise_measurable measurable)) := by
  refine ⟨invariant.probability.map _ _,
    (Measure.eq_iff_lintegral _ _).mpr fun function functionMeasurable => ?_⟩
  have composed := functionMeasurable.comp measurable
  rw [Measure.lintegral_bind _ _ functionMeasurable,
    lintegral_map _ _ _ (Kernel.lintegral_measurable _ functionMeasurable),
    lintegral_map _ _ _ functionMeasurable, ← invariant.mean,
    Measure.lintegral_bind _ _ composed]
  apply lintegral_congr
  intro draws
  rw [lintegral_empirical _ _ functionMeasurable, lintegral_empirical _ _ composed]
  rfl

/-- Mapping every lane's value is an invariant step onto the image target. -/
theorem step_invariant_lanewise {ι : Type} {lanes : Lanes ι} {space : Space α}
    {result : Space β} {source : Measure space} {map : α → β}
    (measurable : MeasurableMap space result map) :
    StepInvariant lanes lanes source (source.map map measurable)
      (Kernel.deterministic (lanewise map) (lanewise_measurable measurable)) := by
  intro population invariant
  rw [Measure.bind_deterministic]
  exact empirical_map measurable invariant

/-! ### Unbiased mass and estimates -/

/-- The population's mean weight `W · (1/N)`, with `W = Σ_j w_j`. -/
@[expose] noncomputable def meanWeight {ι : Type} (lanes : Lanes ι)
    (draws : ι → α × NNReal) : NNReal :=
  lanes.average fun index => (draws index).2

/-- The mass of the empirical measure is the mean weight. -/
theorem empirical_mass {ι : Type} (lanes : Lanes ι) {space : Space α}
    (draws : ι → α × NNReal) :
    empirical lanes space draws Set.univ = ENNReal.finite (meanWeight lanes draws) := by
  have total := lintegral_empirical lanes draws (ENNRealMeasurable.constant space ENNReal.one)
  rw [lintegral_const, ENNReal.one_mul] at total
  rw [total, meanWeight, Lanes.finite_average]
  refine congrArg (ENNReal.mul _) (congrArg finiteSum (List.map_congr_left fun index _ => ?_))
  exact ENNReal.mul_one _

/-- The mean weight is unbiased for the target's mass. -/
theorem empirical_mass_unbiased {ι : Type} {lanes : Lanes ι} {space : Space α}
    {target : Measure space} {population : Measure (populationSpace ι space)}
    (invariant : EmpiricalInvariant lanes target population) :
    lintegral population (fun draws => ENNReal.finite (meanWeight lanes draws)) =
      target Set.univ := by
  rw [← invariant.mean, Measure.bind_apply _ _ space.univ]
  apply lintegral_congr
  intro draws
  exact (empirical_mass lanes draws).symm

/-- The unnormalized estimate `(1/N) Σ_j f(x_j) w_j` of a real integrand. -/
@[expose] noncomputable def unnormalizedEstimate {ι : Type} (lanes : Lanes ι)
    (integrand : α → Carrier) (draws : ι → α × NNReal) : Carrier :=
  lanes.realAverage fun index =>
    Dedekind.mul (integrand (draws index).1) (NNReal.toReal (draws index).2)

/-- A certified integral against a picked lane is the certified integral of the
lane average against the population. Both parts average lane by lane and keep
their masses. -/
theorem hasRealIntegral_of_pick {ι : Type} {lanes : Lanes ι} {space : Space α}
    {population : Measure (populationSpace ι space)}
    {integrand : α × NNReal → Carrier} {value : Carrier}
    (integral : HasRealIntegral (population.bind (pick lanes space)) integrand value) :
    HasRealIntegral population
      (fun draws => lanes.realAverage fun index => integrand (draws index)) value := by
  obtain ⟨parts, same⟩ := integral
  have averageMeasurable : ∀ {part : α × NNReal → NNReal},
      ENNRealMeasurable (Space.product space weightSpace)
        (fun draw => ENNReal.finite (part draw)) →
      ENNRealMeasurable (populationSpace ι space)
        (fun draws => ENNReal.finite (lanes.average fun index => part (draws index))) := by
    intro part measurable
    have equal : (fun draws => ENNReal.finite (lanes.average fun index => part (draws index))) =
        fun draws => lintegral (pick lanes space draws)
          (fun draw => ENNReal.finite (part draw)) :=
      funext fun draws => by rw [lintegral_pick lanes draws measurable, Lanes.finite_average]
    rw [equal]
    exact Kernel.lintegral_measurable _ measurable
  have averageIntegral : ∀ {part : α × NNReal → NNReal} {mass : NNReal},
      ENNRealMeasurable (Space.product space weightSpace)
        (fun draw => ENNReal.finite (part draw)) →
      lintegral (population.bind (pick lanes space)) (fun draw => ENNReal.finite (part draw)) =
        ENNReal.finite mass →
      lintegral population
        (fun draws => ENNReal.finite (lanes.average fun index => part (draws index))) =
        ENNReal.finite mass := by
    intro part mass measurable integral
    rw [← integral, Measure.lintegral_bind _ _ measurable]
    apply lintegral_congr
    intro draws
    rw [lintegral_pick lanes draws measurable, Lanes.finite_average]
  refine ⟨{ positive := fun draws => lanes.average fun index => parts.positive (draws index)
            negative := fun draws => lanes.average fun index => parts.negative (draws index)
            positive_measurable := averageMeasurable parts.positive_measurable
            negative_measurable := averageMeasurable parts.negative_measurable
            decomposition := fun draws => ?_
            positiveMass := parts.positiveMass
            negativeMass := parts.negativeMass
            positive_integral := averageIntegral parts.positive_measurable parts.positive_integral
            negative_integral :=
              averageIntegral parts.negative_measurable parts.negative_integral }, same⟩
  rw [Lanes.toReal_average, Lanes.toReal_average, ← Lanes.realAverage_sub]
  exact congrArg lanes.realAverage (funext fun index => parts.decomposition (draws index))

/-- The weighted average of a real integrand over an invariant population is
unbiased for the integrand's integral against the target. -/
theorem empirical_estimate_unbiased {ι : Type} {lanes : Lanes ι} {space : Space α}
    {target : Measure space} {population : Measure (populationSpace ι space)}
    (invariant : EmpiricalInvariant lanes target population)
    {integrand : α → Carrier} {value : Carrier}
    (integral : HasRealIntegral target integrand value) :
    HasRealIntegral population (unnormalizedEstimate lanes integrand) value :=
  hasRealIntegral_of_pick ((pick_calibrated invariant).hasRealIntegral integral)

end

end Problib.Inference
