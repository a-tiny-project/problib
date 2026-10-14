module

public import Problib.Inference.ExtendedTarget
import Problib.Inference.Reciprocal
import Problib.Measure.Integral.Lebesgue.AlmostEverywhere
import Problib.Measure.Integral.Lebesgue.Extensionality
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Integral.Density.Change
import Problib.Measure.Kernel.Finite
import Problib.Measure.Kernel.Measurable
import Problib.Measure.Kernel.Product
set_option autoImplicit false

/-! # Selecting a lane by weight

Sampling importance resampling with one output draws a lane of a weighted
population with probability proportional to its weight. `selection` draws the
lane from `laneLaw`, which is categorical in the weights and falls back to a
stated Markov kernel at zero total weight, and returns the lane's value with the
population's mean weight `Ẑ`.

The selected value and `Ẑ` are properly weighted for the population's target
whenever the population is invariant for it (`selected_properlyWeighted`):
weighing the lane's law by `Ẑ` gives each lane its share of the weight
(`weighted_laneLaw`), which is the empirical measure. No positivity is needed,
because at zero total weight both sides vanish.

The law of the selected value has no closed form. Its part at positive total
weight, `selectedPositive`, draws the lane from the categorical law alone, which
carries no mass at zero total weight. It is the extended target reweighted by
`1/Ẑ` and read at the marked lane (`selectedPositive_eq_extended`). At almost
surely positive total weight the fallback never fires, and the selected law is
its positive part (`selected_eq_positive`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Analysis (categorical lintegral_categorical categorical_apply
  categorical_isProbability)

variable {α : Type} {space : Space α}

public section

/-! ### The selection kernel -/

/-- The marked lane's value, paired with the population's mean weight. -/
theorem selectedDraw_measurable {ι : Type} (lanes : Lanes ι) (space : Space α) :
    MeasurableMap (markedSpace ι space) (Space.product space weightSpace)
      (fun marked => (reference marked, meanWeight lanes marked.1)) :=
  Space.pair_measurable (reference_measurable lanes space)
    (MeasurableMap.comp (meanWeight_measurable lanes space)
      (Space.first_measurable (populationSpace ι space) (Space.discrete ι)))

/-- Draw a lane from `laneLaw`, and return its value with the population's mean
weight. The fallback draws the lane at zero total weight. -/
@[expose] noncomputable def selection {ι : Type} (lanes : Lanes ι) (space : Space α)
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws)) :
    Kernel (populationSpace ι space) (Space.product space weightSpace) :=
  ((laneLaw lanes space fallback).attach
      (Kernel.IsSFinite.ofMarkov (laneLaw_markov lanes space fallbackMarkov))).map
    (fun marked => (reference marked, meanWeight lanes marked.1))
    (selectedDraw_measurable lanes space)

/-- Integrating against a selection integrates over the lane's law. -/
theorem lintegral_selection {ι : Type} (lanes : Lanes ι) (space : Space α)
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws))
    (draws : ι → α × NNReal) {function : α × NNReal → ENNReal}
    (measurable : ENNRealMeasurable (Space.product space weightSpace) function) :
    lintegral (selection lanes space fallback fallbackMarkov draws) function =
      lintegral (laneLaw lanes space fallback draws)
        (fun lane => function ((draws lane).1, meanWeight lanes draws)) := by
  rw [selection, Kernel.map_apply, Kernel.attach_apply, Measure.map_comp,
    lintegral_map _ _ _ measurable]
  rfl

/-- A selection is a probability. -/
theorem selection_markov {ι : Type} (lanes : Lanes ι) (space : Space α)
    {fallback : Kernel (populationSpace ι space) (Space.discrete ι)}
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws))
    (draws : ι → α × NNReal) :
    Measure.IsProbability (selection lanes space fallback fallbackMarkov draws) := by
  rw [selection, Kernel.map_apply, Kernel.attach_apply]
  exact ((laneLaw_markov lanes space fallbackMarkov draws).map _ _).map _ _

/-- Weighing a selection by its mean weight gives the population's empirical
measure. -/
theorem barycenter_selection {ι : Type} (lanes : Lanes ι) (space : Space α)
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws))
    (draws : ι → α × NNReal) :
    barycenter (selection lanes space fallback fallbackMarkov draws) =
      empirical lanes space draws := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have laneMeasurable : ENNRealMeasurable (Space.discrete ι)
      (fun lane => function (draws lane).1) :=
    ENNRealMeasurable.of_measurableMap (MeasurableMap.from_discrete ennrealBorel _)
  rw [lintegral_barycenter _ measurable,
    lintegral_selection lanes space fallback fallbackMarkov draws
      (weighted_integrand_measurable measurable),
    lintegral_empirical lanes draws measurable]
  show lintegral (laneLaw lanes space fallback draws)
      (fun lane => ENNReal.mul (ENNReal.finite (meanWeight lanes draws))
        (function (draws lane).1)) = _
  rw [lintegral_smul _ _ laneMeasurable]
  exact weighted_laneLaw lanes space fallback draws fun lane => function (draws lane).1

/-- The selected value with the population's mean weight is properly weighted
for the target of an invariant population. No positivity is needed: at zero
total weight both sides of `weighted_laneLaw` vanish. -/
theorem selected_properlyWeighted {ι : Type} {lanes : Lanes ι} {target : Measure space}
    {population : Measure (populationSpace ι space)}
    (invariant : EmpiricalInvariant lanes target population)
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws)) :
    ProperlyWeighted target (population.bind (selection lanes space fallback fallbackMarkov)) := by
  refine ⟨invariant.probability.bind _ (selection_markov lanes space fallbackMarkov), ?_⟩
  have weighed : barycenterKernel (selection lanes space fallback fallbackMarkov) =
      empirical lanes space :=
    Kernel.ext fun draws => barycenter_selection lanes space fallback fallbackMarkov draws
  rw [barycenter_bind, weighed]
  exact invariant.mean

/-! ### The selected law at positive total weight -/

/-- At zero total weight the categorical law of the weights has no mass, and
otherwise it is a probability. -/
theorem categoricalKernel_finite {ι : Type} (lanes : Lanes ι) (space : Space α)
    (draws : ι → α × NNReal) :
    Measure.IsFinite (categoricalKernel lanes space draws) := by
  by_cases zero : totalWeight lanes draws = NNReal.zero
  · constructor
    show ENNReal.Finite (categorical lanes.list (fun lane => (draws lane).2) Set.univ)
    rw [categorical_apply]
    have vanishes := ENNReal.additiveLaws.listSum_map_eq_zero lanes.list
      (fun lane => ENNReal.mul
        (Analysis.categoricalShare lanes.list (fun lane => (draws lane).2) lane)
        (Measure.dirac (Space.discrete ι) lane Set.univ))
      fun lane _ => by
        show ENNReal.mul (ENNReal.finite (NNReal.div (draws lane).2 _)) _ = ENNReal.zero
        rw [weight_eq_zero zero lane, NNReal.zero_div]
        exact ENNReal.zero_mul _
    rw [vanishes]
    exact True.intro
  · constructor
    show ENNReal.Finite (categorical lanes.list (fun lane => (draws lane).2) Set.univ)
    rw [(categorical_isProbability lanes.list zero).univ_eq_one]
    exact True.intro

/-- The categorical law of the weights, as an s-finite kernel. -/
noncomputable def categoricalKernel_sfinite {ι : Type} (lanes : Lanes ι) (space : Space α) :
    Kernel.IsSFinite (categoricalKernel lanes space) :=
  Kernel.IsSFinite.ofFiniteFibers (categoricalKernel_finite lanes space)

/-- The selected lane's value at positive total weight: the lane is drawn from
the categorical law of the weights, which has no mass at zero total weight. -/
@[expose] noncomputable def selectedPositive {ι : Type} (lanes : Lanes ι)
    (population : Measure (populationSpace ι space)) : Measure space :=
  (population.semiproduct (categoricalKernel lanes space)
    (categoricalKernel_sfinite lanes space)).map reference (reference_measurable lanes space)

/-- Integrating against the positive part integrates over the categorical lane. -/
theorem lintegral_selectedPositive {ι : Type} (lanes : Lanes ι)
    (population : Measure (populationSpace ι space)) {function : α → ENNReal}
    (measurable : ENNRealMeasurable space function) :
    lintegral (selectedPositive lanes population) function =
      lintegral population (fun draws =>
        lintegral (categorical lanes.list fun lane => (draws lane).2)
          (fun lane => function (draws lane).1)) := by
  rw [selectedPositive, lintegral_map _ _ _ measurable,
    lintegral_semiproduct _ _ _ (measurable.comp (reference_measurable lanes space))]
  rfl

/-- At almost surely positive total weight the fallback never fires, so the
selected value's law is its positive part. -/
theorem selected_eq_positive {ι : Type} (lanes : Lanes ι)
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws))
    {population : Measure (populationSpace ι space)}
    (positive : population.AE fun draws => totalWeight lanes draws ≠ NNReal.zero) :
    (population.bind (selection lanes space fallback fallbackMarkov)).map Prod.fst
        (draw_value_measurable space) =
      selectedPositive lanes population := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have valueMeasurable := measurable.comp (draw_value_measurable space)
  rw [lintegral_map _ _ _ measurable, Measure.lintegral_bind _ _ valueMeasurable,
    lintegral_selectedPositive lanes population measurable]
  refine lintegral_congr_ae (positive.mono fun draws nonzero => ?_)
  show lintegral (selection lanes space fallback fallbackMarkov draws)
      (fun draw => function draw.1) = _
  rw [lintegral_selection lanes space fallback fallbackMarkov draws valueMeasurable,
    laneLaw_positive lanes space fallback draws nonzero]

/-! ### The positive part through the extended target -/

/-- The inverse mean weight `1/Ẑ` of a marked population, read as zero at zero
mean weight. -/
@[expose] noncomputable def inverseMeanWeight {ι : Type} (lanes : Lanes ι)
    (marked : (ι → α × NNReal) × ι) : ENNReal :=
  ENNReal.finite (NNReal.div NNReal.one (meanWeight lanes marked.1))

theorem inverseMeanWeight_measurable {ι : Type} (lanes : Lanes ι) (space : Space α) :
    ENNRealMeasurable (markedSpace ι space) (inverseMeanWeight (α := α) lanes) :=
  finite_weight_measurable (weight_inverse_measurable
    (MeasurableMap.comp (meanWeight_measurable lanes space)
      (Space.first_measurable (populationSpace ι space) (Space.discrete ι))))

/-- A lane's share `1/N` is not zero. -/
theorem share_ne_zero {ι : Type} (lanes : Lanes ι) : lanes.share ≠ NNReal.zero := by
  intro zero
  have unit := lanes.share_mul_count
  rw [zero, NNReal.zero_mul] at unit
  exact NNReal.one_ne_zero unit.symm

/-- At positive total weight the mean weight is positive. -/
theorem meanWeight_ne_zero {ι : Type} (lanes : Lanes ι) {draws : ι → α × NNReal}
    (positive : totalWeight lanes draws ≠ NNReal.zero) :
    meanWeight lanes draws ≠ NNReal.zero := by
  rw [meanWeight_eq]
  intro zero
  rcases NNReal.mul_eq_zero_iff.mp zero with share | total
  · exact share_ne_zero lanes share
  · exact positive total

/-- Weighing each lane by its share of the weight and by `1/Ẑ` draws it from
the categorical law of the weights. At zero total weight both sides vanish. -/
theorem lintegral_categorical_marked {ι : Type} (lanes : Lanes ι)
    (draws : ι → α × NNReal) (values : ι → ENNReal) :
    lintegral (categorical lanes.list fun lane => (draws lane).2) values =
      ENNReal.mul (ENNReal.finite lanes.share)
        (ENNReal.additiveLaws.listSum (lanes.list.map fun lane =>
          ENNReal.mul (drawWeight (draws lane))
            (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one (meanWeight lanes draws)))
              (values lane)))) := by
  by_cases zero : totalWeight lanes draws = NNReal.zero
  · have left : ENNReal.additiveLaws.listSum (lanes.list.map fun lane => ENNReal.mul
        (ENNReal.finite (NNReal.div (draws lane).2 (totalWeight lanes draws))) (values lane)) =
        ENNReal.zero :=
      ENNReal.additiveLaws.listSum_map_eq_zero lanes.list _ fun lane _ => by
        rw [weight_eq_zero zero lane, NNReal.zero_div]
        exact ENNReal.zero_mul _
    have right : ENNReal.additiveLaws.listSum (lanes.list.map fun lane =>
        ENNReal.mul (drawWeight (draws lane))
          (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one (meanWeight lanes draws)))
            (values lane))) = ENNReal.zero :=
      ENNReal.additiveLaws.listSum_map_eq_zero lanes.list _ fun lane _ => by
        rw [drawWeight, weight_eq_zero zero lane]
        exact ENNReal.zero_mul _
    rw [lintegral_categorical]
    exact left.trans (by rw [right, ENNReal.mul_zero])
  · have weighed := weighted_laneLaw lanes (Space.discrete α)
      (categoricalKernel lanes (Space.discrete α)) draws values
    rw [laneLaw_positive lanes (Space.discrete α) _ draws zero] at weighed
    have pulled := ENNReal.semiring.listSum_map_mul_left lanes.list
      (ENNReal.finite (NNReal.div NNReal.one (meanWeight lanes draws)))
      fun lane => ENNReal.mul (drawWeight (draws lane)) (values lane)
    have inverse : ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one (meanWeight lanes draws)))
        (ENNReal.finite (meanWeight lanes draws)) = ENNReal.one := by
      rw [ENNReal.finite_mul_finite, NNReal.div_mul_cancel _ (meanWeight_ne_zero lanes zero)]
      rfl
    have reorder : ∀ lane, ENNReal.mul (drawWeight (draws lane))
        (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one (meanWeight lanes draws)))
          (values lane)) =
        ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one (meanWeight lanes draws)))
          (ENNReal.mul (drawWeight (draws lane)) (values lane)) := fun lane => by
      rw [← ENNReal.mul_assoc, ENNReal.mul_comm (drawWeight (draws lane)), ENNReal.mul_assoc]
    simp only [reorder]
    rw [pulled, ← ENNReal.mul_assoc, ENNReal.mul_comm (ENNReal.finite lanes.share),
      ENNReal.mul_assoc, ← weighed, ← ENNReal.mul_assoc, inverse, ENNReal.one_mul]

/-- The positive part of the selected law is the extended target reweighted by
the inverse mean weight and read at the marked lane. -/
theorem selectedPositive_eq_extended {ι : Type} (lanes : Lanes ι)
    (population : Measure (populationSpace ι space)) :
    selectedPositive lanes population =
      ((extended lanes population).withDensity (inverseMeanWeight lanes)).map reference
        (reference_measurable lanes space) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have readMeasurable := measurable.comp (reference_measurable lanes space)
  have inverseMeasurable := inverseMeanWeight_measurable lanes space
  rw [lintegral_selectedPositive lanes population measurable, lintegral_map _ _ _ measurable,
    lintegral_withDensity _ inverseMeasurable readMeasurable, extended,
    Measure.lintegral_bind _ _ (ENNRealMeasurable.mul inverseMeasurable readMeasurable)]
  refine lintegral_congr _ fun draws => ?_
  rw [lintegral_markedLane lanes draws (ENNRealMeasurable.mul inverseMeasurable readMeasurable)]
  exact lintegral_categorical_marked lanes draws fun lane => function (draws lane).1

end

end Problib.Inference
