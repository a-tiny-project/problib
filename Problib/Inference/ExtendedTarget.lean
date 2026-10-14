module

public import Problib.Inference.Involutive
public import Problib.Inference.Population
public import Problib.Inference.Resampling.Ancestors
public import Problib.Measure.Integral.Density.Basic
import Problib.Measure.Integral.Density.Change
import Problib.Measure.Integral.Lebesgue.Extensionality
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Kernel.Composition.Bind.Transport
import Problib.Measure.Kernel.Measurable
import Problib.Measure.Kernel.Piecewise
import Problib.Measure.Kernel.Precomp
import Problib.Measure.Product.Countable
set_option autoImplicit false

/-! # Extended targets and their invariant transitions

A transition on a larger space can keep a target on a smaller one. Read the
larger space through a measurable `read`, and let `conditional` disintegrate a
measure `J` on it along `read`. Refreshing from `conditional`, moving by any
kernel that keeps `J`, and reading again keeps `J`'s image under `read`
(`referenceChain_invariant`). The statement needs no product structure, no
density and no finiteness. `gibbs_invariant` is its case where `read` is the
first projection and `conditional x` is `δ_x ⊗ c x`.

A population with one lane marked is such a larger space. `markedLane` marks
each lane at its share of the weight, `(1/N) w_k δ_(draws, k)`, and
`extended lanes P` is Andrieu, Doucet and Holenstein's extended target: a
population drawn from `P`, with lane `k` marked at weight `w_k / N`. Read at the
marked lane's value, it is `P`'s expected empirical measure
(`extended_reference`), for any law of populations `P`.

Redrawing the marked lane from the categorical law of the weights keeps the
extended target (`laneRefresh_invariant`). At total weight zero the extended
target has no mass, so the theorem holds for any Markov fallback there.

A move of the second block at each first block keeps a joint law
`prior ⋉ fibers` when it keeps every fiber (`fiberwise_invariant`). That is the
value block of a two-block sampler. -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Analysis (categorical categoricalShare lintegral_categorical
  categorical_isProbability)

universe u v

public section

/-! ### Reading an extended space -/

/-- Refresh an extended state from `conditional` at the current point, move it
by `move`, and read the new point. -/
@[expose] noncomputable def referenceChain {ε : Type u} {χ : Type v}
    {extendedSpace : Space ε} {space : Space χ}
    (read : ε → χ) (readMeasurable : MeasurableMap extendedSpace space read)
    (conditional : Kernel space extendedSpace) (move : Kernel extendedSpace extendedSpace) :
    Kernel space space :=
  (conditional.comp move).map read readMeasurable

/-- If `conditional` disintegrates `target` along `read`, and `move` keeps
`target`, then refreshing, moving and reading keeps `target`'s image under
`read`. The measures and kernels may be infinite: the identity is one of
measures, and no step normalizes. -/
theorem referenceChain_invariant {ε : Type u} {χ : Type v}
    {extendedSpace : Space ε} {space : Space χ}
    (target : Measure extendedSpace) (read : ε → χ)
    (readMeasurable : MeasurableMap extendedSpace space read)
    (conditional : Kernel space extendedSpace)
    (disintegrates : (target.map read readMeasurable).bind conditional = target)
    (move : Kernel extendedSpace extendedSpace) (keeps : KernelInvariant target move) :
    KernelInvariant (target.map read readMeasurable)
      (referenceChain read readMeasurable conditional move) := by
  unfold KernelInvariant referenceChain
  rw [← Measure.map_bind, ← Measure.bind_assoc, disintegrates, keeps]

/-! ### Fiberwise moves -/

/-- Keeping the first block of a pair and replacing its second block. -/
theorem keepFirst_measurable {θ : Type u} {χ : Type v}
    (parameters : Space θ) (values : Space χ) :
    MeasurableMap (Space.product (Space.product parameters values) values)
      (Space.product parameters values)
      (fun pair : (θ × χ) × χ => (pair.1.1, pair.2)) :=
  Space.pair_measurable
    (MeasurableMap.comp (Space.first_measurable parameters values)
      (Space.first_measurable (Space.product parameters values) values))
    (Space.second_measurable (Space.product parameters values) values)

/-- Move the second block by `move` at the current pair, and keep the first
block. -/
@[expose] noncomputable def fiberwise {θ : Type u} {χ : Type v}
    {parameters : Space θ} {values : Space χ}
    (move : Kernel (Space.product parameters values) values)
    (moveFinite : Kernel.IsSFinite move) :
    Kernel (Space.product parameters values) (Space.product parameters values) :=
  (Kernel.attach move moveFinite).map (fun pair => (pair.1.1, pair.2))
    (keepFirst_measurable parameters values)

/-- A move that keeps each fiber `fibers θ` at its parameter keeps the joint law
`prior ⋉ fibers`. The prior and the fibers need only be s-finite. -/
theorem fiberwise_invariant {θ : Type u} {χ : Type v}
    {parameters : Space θ} {values : Space χ}
    (prior : Measure parameters) (fibers : Kernel parameters values)
    (fibersFinite : Kernel.IsSFinite fibers)
    (move : Kernel (Space.product parameters values) values)
    (moveFinite : Kernel.IsSFinite move)
    (keeps : ∀ parameter, KernelInvariant (fibers parameter)
      (move.precomp (fun value => (parameter, value)) (Kernel.pair_left_measurable parameter))) :
    KernelInvariant (prior.semiproduct fibers fibersFinite) (fiberwise move moveFinite) := by
  unfold KernelInvariant Measure.semiproduct
  rw [Measure.bind_assoc]
  refine congrArg prior.bind (Kernel.ext fun parameter => ?_)
  rw [Kernel.comp_apply, Kernel.attach_apply, Measure.bind_map]
  have fiber : (fiberwise move moveFinite).precomp (fun value => (parameter, value))
      (Kernel.pair_left_measurable parameter) =
      (move.precomp (fun value => (parameter, value))
        (Kernel.pair_left_measurable parameter)).map
        (fun value => (parameter, value)) (Kernel.pair_left_measurable parameter) :=
    Kernel.ext fun value => Measure.map_comp (move (parameter, value))
      (fun next => ((parameter, value), next)) (fun pair => (pair.1.1, pair.2))
      (Kernel.pair_left_measurable (parameter, value)) (keepFirst_measurable parameters values)
  rw [fiber, ← Measure.map_bind, keeps parameter]

/-! ### The extended target of a population -/

variable {α : Type} {space : Space α}

/-- A population with one lane marked. -/
abbrev markedSpace (ι : Type) (space : Space α) : Space ((ι → α × NNReal) × ι) :=
  Space.product (populationSpace ι space) (Space.discrete ι)

theorem markLane_measurable {ι : Type} (space : Space α) (lane : ι) :
    MeasurableMap (populationSpace ι space) (markedSpace ι space)
      (fun draws => (draws, lane)) :=
  Space.pair_measurable (MeasurableMap.identity _) (MeasurableMap.constant _ _ lane)

/-- Each lane marked at its share of the weight, `(1/N) Σ_k w_k δ_(draws, k)`.
Its mass is the mean weight. -/
@[expose] noncomputable def markedLane {ι : Type} (lanes : Lanes ι) (space : Space α) :
    Kernel (populationSpace ι space) (markedSpace ι space) where
  toFun := fun draws => Measure.smul (ENNReal.finite lanes.share)
    (Measure.listSum (lanes.list.map fun lane =>
      Measure.smul (drawWeight (draws lane)) (Measure.dirac _ (draws, lane))))
  measurable := by
    intro set setMeasurable
    have equal : (fun draws : ι → α × NNReal => Measure.smul (ENNReal.finite lanes.share)
        (Measure.listSum (lanes.list.map fun lane =>
          Measure.smul (drawWeight (draws lane))
            (Measure.dirac (markedSpace ι space) (draws, lane)))) set) =
        fun draws => ENNReal.mul (ENNReal.finite lanes.share)
          (ENNReal.additiveLaws.listSum (lanes.list.map fun lane =>
            ENNReal.mul (drawWeight (draws lane))
              (Kernel.deterministic (fun draws : ι → α × NNReal => (draws, lane))
                (markLane_measurable space lane) draws set))) := by
      funext draws
      rw [Measure.smul_apply_measurable _ _ setMeasurable,
        Measure.listSum_apply _ setMeasurable, List.map_map]
      refine congrArg (ENNReal.mul _)
        (congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun lane _ => ?_))
      exact Measure.smul_apply_measurable _ _ setMeasurable
    rw [equal]
    exact (ENNRealMeasurable.listSum_map lanes.list fun lane =>
      ENNRealMeasurable.mul ((drawWeight_measurable space).comp (lane_measurable space lane))
        ((Kernel.deterministic _ (markLane_measurable space lane)).measurable
          setMeasurable)).const_mul _

theorem markedLane_apply {ι : Type} (lanes : Lanes ι) (space : Space α)
    (draws : ι → α × NNReal) :
    markedLane lanes space draws = Measure.smul (ENNReal.finite lanes.share)
      (Measure.listSum (lanes.list.map fun lane =>
        Measure.smul (drawWeight (draws lane)) (Measure.dirac _ (draws, lane)))) :=
  rfl

/-- Integrating against the marked lanes averages the weighted integrand over
the lanes. -/
theorem lintegral_markedLane {ι : Type} (lanes : Lanes ι) {space : Space α}
    (draws : ι → α × NNReal) {function : (ι → α × NNReal) × ι → ENNReal}
    (measurable : ENNRealMeasurable (markedSpace ι space) function) :
    lintegral (markedLane lanes space draws) function =
      ENNReal.mul (ENNReal.finite lanes.share)
        (ENNReal.additiveLaws.listSum (lanes.list.map fun lane =>
          ENNReal.mul (drawWeight (draws lane)) (function (draws, lane)))) := by
  rw [markedLane_apply, lintegral_smul_measure, lintegral_listSum, List.map_map]
  refine congrArg (ENNReal.mul _)
    (congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun lane _ => ?_))
  show lintegral (Measure.smul _ _) function = _
  rw [lintegral_smul_measure, lintegral_dirac _ _ measurable]

/-- Andrieu, Doucet and Holenstein's extended target: a population drawn from
`population`, with lane `k` marked at weight `w_k / N`. It is stated for any
law of populations, and needs no density of any proposal. -/
@[expose] noncomputable def extended {ι : Type} (lanes : Lanes ι)
    (population : Measure (populationSpace ι space)) : Measure (markedSpace ι space) :=
  population.bind (markedLane lanes space)

/-- The value of the marked lane. -/
@[expose] def reference {ι : Type} (marked : (ι → α × NNReal) × ι) : α :=
  (marked.1 marked.2).1

theorem reference_measurable {ι : Type} (lanes : Lanes ι) (space : Space α) :
    MeasurableMap (markedSpace ι space) space (reference (α := α) (ι := ι)) :=
  MeasurableMap.comp (Space.first_measurable space weightSpace)
    (MeasurableMap.comp
      (MeasurableMap.uncurry_of_countable_first (source := populationSpace ι space)
        (target := Space.product space weightSpace) lanes.position lanes.position_injective
        (function := fun lane draws => draws lane) fun lane => lane_measurable space lane)
      (Space.swap_measurable (populationSpace ι space) (Space.discrete ι)))

/-- Read at the marked lane's value, the extended target is the population's
expected empirical measure. -/
theorem extended_reference {ι : Type} (lanes : Lanes ι)
    (population : Measure (populationSpace ι space)) :
    (extended lanes population).map reference (reference_measurable lanes space) =
      population.bind (empirical lanes space) := by
  unfold extended
  rw [Measure.map_bind]
  refine congrArg population.bind (Kernel.ext fun draws => ?_)
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [Kernel.map_apply, lintegral_map _ _ _ measurable,
    lintegral_markedLane lanes draws (measurable.comp (reference_measurable lanes space)),
    lintegral_empirical lanes draws measurable]
  rfl

/-- An invariant population's extended target reads its target at the marked
lane. -/
theorem extended_reference_of_invariant {ι : Type} {lanes : Lanes ι}
    {target : Measure space} {population : Measure (populationSpace ι space)}
    (invariant : EmpiricalInvariant lanes target population) :
    (extended lanes population).map reference (reference_measurable lanes space) = target :=
  (extended_reference lanes population).trans invariant.mean

/-! ### Refreshing the marked lane -/

/-- The marked lane's law given the population: categorical in the weights, and
`fallback` at total weight zero. -/
@[expose] noncomputable def laneLaw {ι : Type} (lanes : Lanes ι) (space : Space α)
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι)) :
    Kernel (populationSpace ι space) (Space.discrete ι) :=
  Kernel.piecewise (zeroTotal lanes) (zeroTotal_measurable lanes space) fallback
    (categoricalKernel lanes space)

theorem laneLaw_positive {ι : Type} (lanes : Lanes ι) (space : Space α)
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (draws : ι → α × NNReal) (positive : totalWeight lanes draws ≠ NNReal.zero) :
    laneLaw lanes space fallback draws = categorical lanes.list fun lane => (draws lane).2 :=
  Kernel.piecewise_apply_of_not_mem _ _ _ _ draws fun zero =>
    positive ((zeroTotal_iff lanes draws).mp zero)

/-- The marked lane's law is a probability when the fallback is one. -/
theorem laneLaw_markov {ι : Type} (lanes : Lanes ι) (space : Space α)
    {fallback : Kernel (populationSpace ι space) (Space.discrete ι)}
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws))
    (draws : ι → α × NNReal) :
    Measure.IsProbability (laneLaw lanes space fallback draws) := by
  by_cases zero : totalWeight lanes draws = NNReal.zero
  · unfold laneLaw
    rw [Kernel.piecewise_apply_of_mem _ _ _ _ draws ((zeroTotal_iff lanes draws).mpr zero)]
    exact fallbackMarkov draws
  · rw [laneLaw_positive lanes space fallback draws zero]
    exact categorical_isProbability lanes.list zero

/-- Redraw the marked lane from `laneLaw`, and keep the population. -/
@[expose] noncomputable def laneRefresh {ι : Type} (lanes : Lanes ι) (space : Space α)
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws)) :
    Kernel (markedSpace ι space) (markedSpace ι space) :=
  gibbsKernel (laneLaw lanes space fallback)
    (Kernel.IsSFinite.ofMarkov (laneLaw_markov lanes space fallbackMarkov))

/-- Weighing the marked lane's law by the mean weight gives each lane its share
of the weight, `(1/N) w_k`. At total weight zero both sides vanish, so the
fallback does not enter. -/
theorem weighted_laneLaw {ι : Type} (lanes : Lanes ι) (space : Space α)
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (draws : ι → α × NNReal) (function : ι → ENNReal) :
    ENNReal.mul (ENNReal.finite (meanWeight lanes draws))
        (lintegral (laneLaw lanes space fallback draws) function) =
      ENNReal.mul (ENNReal.finite lanes.share)
        (ENNReal.additiveLaws.listSum (lanes.list.map fun lane =>
          ENNReal.mul (drawWeight (draws lane)) (function lane))) := by
  by_cases zero : totalWeight lanes draws = NNReal.zero
  · have terms : ENNReal.additiveLaws.listSum (lanes.list.map fun lane =>
        ENNReal.mul (drawWeight (draws lane)) (function lane)) = ENNReal.zero :=
      ENNReal.additiveLaws.listSum_map_eq_zero lanes.list _ fun lane _ => by
        rw [drawWeight, weight_eq_zero zero lane]
        exact ENNReal.zero_mul _
    rw [terms, ENNReal.mul_zero, meanWeight_eq, zero, NNReal.mul_zero]
    exact ENNReal.zero_mul _
  · rw [laneLaw_positive lanes space fallback draws zero, lintegral_categorical, meanWeight_eq]
    have left := ENNReal.semiring.listSum_map_mul_left lanes.list (ENNReal.finite lanes.share)
      fun lane => ENNReal.mul (drawWeight (draws lane)) (function lane)
    have right := ENNReal.semiring.listSum_map_mul_left lanes.list
      (ENNReal.finite (NNReal.mul lanes.share (totalWeight lanes draws)))
      fun lane => ENNReal.mul (categoricalShare lanes.list (fun lane => (draws lane).2) lane)
        (function lane)
    refine right.symm.trans (Eq.trans ?_ left)
    refine congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun lane _ => ?_)
    show ENNReal.mul (ENNReal.finite (NNReal.mul lanes.share (totalWeight lanes draws)))
        (ENNReal.mul (categoricalShare lanes.list (fun lane => (draws lane).2) lane)
          (function lane)) =
      ENNReal.mul (ENNReal.finite lanes.share)
        (ENNReal.mul (drawWeight (draws lane)) (function lane))
    rw [← ENNReal.mul_assoc, ← ENNReal.mul_assoc]
    refine congrArg (fun factor => ENNReal.mul factor (function lane)) ?_
    show ENNReal.mul (ENNReal.finite (NNReal.mul lanes.share (totalWeight lanes draws)))
        (ENNReal.finite (NNReal.div (draws lane).2 (totalWeight lanes draws))) =
      ENNReal.mul (ENNReal.finite lanes.share) (ENNReal.finite (draws lane).2)
    rw [ENNReal.finite_mul_finite, ENNReal.finite_mul_finite, NNReal.mul_assoc,
      NNReal.mul_div_cancel _ zero]

/-- The extended target is the population weighted by its mean weight, with the
marked lane drawn from `laneLaw`. -/
theorem extended_eq_semiproduct {ι : Type} (lanes : Lanes ι)
    (population : Measure (populationSpace ι space))
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws)) :
    extended lanes population =
      (population.withDensity fun draws => ENNReal.finite (meanWeight lanes draws)).semiproduct
        (laneLaw lanes space fallback)
        (Kernel.IsSFinite.ofMarkov (laneLaw_markov lanes space fallbackMarkov)) := by
  have densityMeasurable : ENNRealMeasurable (populationSpace ι space)
      fun draws => ENNReal.finite (meanWeight lanes draws) :=
    finite_weight_measurable (meanWeight_measurable lanes space)
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have sliceMeasurable : ENNRealMeasurable (populationSpace ι space) fun draws =>
      lintegral (laneLaw lanes space fallback draws) fun lane => function (draws, lane) :=
    Kernel.lintegral_measurable_joint _
      (Kernel.IsSFinite.ofMarkov (laneLaw_markov lanes space fallbackMarkov))
      (function := fun draws lane => function (draws, lane)) measurable
  unfold extended
  rw [Measure.lintegral_bind _ _ measurable, lintegral_semiproduct _ _ _ measurable,
    lintegral_withDensity _ densityMeasurable sliceMeasurable]
  refine lintegral_congr _ fun draws => ?_
  rw [lintegral_markedLane lanes draws measurable]
  exact (weighted_laneLaw lanes space fallback draws fun lane => function (draws, lane)).symm

/-- Redrawing the marked lane from the categorical law of the weights keeps the
extended target of any law of populations. It holds for any measurable Markov
fallback, because populations of total weight zero, where the fallback acts,
are null under the extended target. The fallback is Markov because the refresh
is a transition. A runnable chain still has to fix one fallback. -/
theorem laneRefresh_invariant {ι : Type} (lanes : Lanes ι)
    (population : Measure (populationSpace ι space))
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws)) :
    KernelInvariant (extended lanes population)
      (laneRefresh lanes space fallback fallbackMarkov) := by
  rw [extended_eq_semiproduct lanes population fallback fallbackMarkov]
  exact gibbs_invariant _ _ _ (laneLaw_markov lanes space fallbackMarkov)

end

end Problib.Inference
