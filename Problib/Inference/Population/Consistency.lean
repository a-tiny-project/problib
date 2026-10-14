import Problib.Inference.Resampling
import Problib.Inference.Resampling.Ancestors
import Problib.Inference.Derivative.Continuous.Integral
import Problib.Measure.Convergence

set_option autoImplicit false

/-! Consistency of populations of weighted draws.

A population's unnormalized estimate `(1/N) Σ_j f(x_j) w_j` is unbiased for
the target's integral of `f` when the population is invariant
(`empirical_estimate_unbiased`). Unbiasedness alone does not make it converge:
one draw copied into every lane is invariant and never converges. Consistency
needs the lanes to fluctuate independently. This file measures the fluctuation
by the mean square error of the estimate and carries a bound on it of the form
`constant · r² / N`, for every reading bounded by `r`, through each stage of a
sequential Monte Carlo run (`EmpiricalL2`).

The lane average of readings whose distinct pairs integrate to the product of
their means has mean square error at most `1/N` times a bound on the second
moments (`lane_variance`). Given the population, a propagation step moves each
lane by one weighted kernel and its lanes are pairwise independent
(`PairwiseProduct`), and multinomial resampling draws its parents independently
(`IndependentAncestors`). Each stage then adds its conditional variance to the
mean square error of its conditional mean (`meanSquare_bind`). Over a finite
horizon with bounded weights the constant stays fixed as `N` grows, so the
self-normalized estimate converges in probability to the target's normalized
integral (`population_consistent`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction
open Problib.Analysis (categorical categoricalShare categorical_isProbability
  hasRealIntegral_categorical)
open Problib.Analysis.Real (abs abs_nonnegative abs_mul abs_le le_abs abs_measurable
  abs_mul_self_le_of_abs_le)
open Problib.Inference.Derivative.Continuous (hasRealIntegral_dirac hasRealIntegral_of_map
  hasRealIntegral_map)

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ### Independent pairs -/

/-- Two readings of one law are independent with the given marginal laws:
every measurable function of the pair integrates as the iterated integral over
the two marginals. -/
def IndependentPair {space : Space α} {target : Space β} (measure : Measure space)
    (first second : α → β) (firstLaw secondLaw : Measure target) : Prop :=
  ∀ function : β × β → ENNReal, ENNRealMeasurable (Space.product target target) function →
    lintegral measure (fun x => function (first x, second x)) =
      lintegral firstLaw fun value => lintegral secondLaw fun other => function (value, other)

section Pair

variable {space : Space α} {target : Space β} {measure : Measure space}
  {first second : α → β} {firstLaw secondLaw : Measure target}

/-- One nonnegative reading of each of an independent pair multiplies their
integrals. -/
private theorem lintegral_pair_mass
    (independent : IndependentPair measure first second firstLaw secondLaw)
    {left right : β → NNReal} {leftMass rightMass : NNReal}
    (leftMeasurable : ENNRealMeasurable target fun value => ENNReal.finite (left value))
    (rightMeasurable : ENNRealMeasurable target fun value => ENNReal.finite (right value))
    (leftIntegral :
      lintegral firstLaw (fun value => ENNReal.finite (left value)) = ENNReal.finite leftMass)
    (rightIntegral :
      lintegral secondLaw (fun value => ENNReal.finite (right value)) = ENNReal.finite rightMass) :
    lintegral measure
        (fun x => ENNReal.finite (NNReal.mul (left (first x)) (right (second x)))) =
      ENNReal.finite (NNReal.mul leftMass rightMass) := by
  have joint : ENNRealMeasurable (Space.product target target) fun pair : β × β =>
      ENNReal.mul (ENNReal.finite (left pair.1)) (ENNReal.finite (right pair.2)) :=
    (ENNRealMeasurable.comp (map := fun value => ENNReal.finite (left value)) leftMeasurable
      (Space.first_measurable _ _)).mul
    (ENNRealMeasurable.comp (map := fun value => ENNReal.finite (right value)) rightMeasurable
      (Space.second_measurable _ _))
  change lintegral _ (fun x => (fun pair : β × β =>
    ENNReal.mul (ENNReal.finite (left pair.1)) (ENNReal.finite (right pair.2)))
      (first x, second x)) = _
  rw [independent _ joint]
  have inner : ∀ value, lintegral secondLaw (fun other =>
      ENNReal.mul (ENNReal.finite (left value)) (ENNReal.finite (right other))) =
      ENNReal.mul (ENNReal.finite rightMass) (ENNReal.finite (left value)) := fun value => by
    rw [lintegral_smul _ _ rightMeasurable, rightIntegral, ENNReal.mul_comm]
  refine (lintegral_congr _ inner).trans ?_
  rw [lintegral_smul _ _ leftMeasurable, leftIntegral, ENNReal.mul_comm]
  rfl

/-- A product of two differences, expanded into like and unlike signs. -/
private theorem mul_sub_sub (a b c d : Carrier) :
    Dedekind.mul (Dedekind.sub a b) (Dedekind.sub c d) =
      Dedekind.sub (Dedekind.add (Dedekind.mul a c) (Dedekind.mul b d))
        (Dedekind.add (Dedekind.mul a d) (Dedekind.mul b c)) := by
  rw [Dedekind.sub_mul, Dedekind.mul_sub, Dedekind.mul_sub]
  simp only [Dedekind.sub_eq_add_neg, Dedekind.neg_add, Dedekind.neg_neg]
  simp only [Dedekind.add_assoc, Dedekind.add_comm, Dedekind.add_left_comm]

/-- The readings of an independent pair multiply their certified integrals.
The positive part pairs like signs and the negative part pairs unlike ones,
and each pairing integrates by the pair law. -/
theorem hasRealIntegral_pair_mul
    (independent : IndependentPair measure first second firstLaw secondLaw)
    (firstMeasurable : MeasurableMap space target first)
    (secondMeasurable : MeasurableMap space target second)
    {left right : β → Carrier} {leftValue rightValue : Carrier}
    (leftIntegral : HasRealIntegral firstLaw left leftValue)
    (rightIntegral : HasRealIntegral secondLaw right rightValue) :
    HasRealIntegral measure (fun x => Dedekind.mul (left (first x)) (right (second x)))
      (Dedekind.mul leftValue rightValue) := by
  obtain ⟨leftParts, leftSame⟩ := leftIntegral
  obtain ⟨rightParts, rightSame⟩ := rightIntegral
  have pairing : ∀ {one other : β → NNReal},
      ENNRealMeasurable target (fun value => ENNReal.finite (one value)) →
      ENNRealMeasurable target (fun value => ENNReal.finite (other value)) →
      ENNRealMeasurable space
        fun x => ENNReal.finite (NNReal.mul (one (first x)) (other (second x))) :=
    fun {one other} oneMeasurable otherMeasurable =>
      (ENNRealMeasurable.comp (map := fun value => ENNReal.finite (one value)) oneMeasurable
        firstMeasurable).mul
      (ENNRealMeasurable.comp (map := fun value => ENNReal.finite (other value)) otherMeasurable
        secondMeasurable)
  refine ⟨{ positive := fun x =>
              NNReal.add (NNReal.mul (leftParts.positive (first x))
                  (rightParts.positive (second x)))
                (NNReal.mul (leftParts.negative (first x)) (rightParts.negative (second x)))
            negative := fun x =>
              NNReal.add (NNReal.mul (leftParts.positive (first x))
                  (rightParts.negative (second x)))
                (NNReal.mul (leftParts.negative (first x)) (rightParts.positive (second x)))
            positive_measurable :=
              (pairing leftParts.positive_measurable rightParts.positive_measurable).add
                (pairing leftParts.negative_measurable rightParts.negative_measurable)
            negative_measurable :=
              (pairing leftParts.positive_measurable rightParts.negative_measurable).add
                (pairing leftParts.negative_measurable rightParts.positive_measurable)
            decomposition := fun x => by
              rw [leftParts.decomposition, rightParts.decomposition, mul_sub_sub]
              rfl
            positiveMass := NNReal.add (NNReal.mul leftParts.positiveMass rightParts.positiveMass)
              (NNReal.mul leftParts.negativeMass rightParts.negativeMass)
            negativeMass := NNReal.add (NNReal.mul leftParts.positiveMass rightParts.negativeMass)
              (NNReal.mul leftParts.negativeMass rightParts.positiveMass)
            positive_integral := by
              change lintegral _ (fun x => ENNReal.add
                (ENNReal.finite (NNReal.mul (leftParts.positive (first x))
                  (rightParts.positive (second x))))
                (ENNReal.finite (NNReal.mul (leftParts.negative (first x))
                  (rightParts.negative (second x))))) = _
              rw [lintegral_add _ (pairing leftParts.positive_measurable
                  rightParts.positive_measurable)
                  (pairing leftParts.negative_measurable rightParts.negative_measurable),
                lintegral_pair_mass independent leftParts.positive_measurable
                  rightParts.positive_measurable leftParts.positive_integral
                  rightParts.positive_integral,
                lintegral_pair_mass independent leftParts.negative_measurable
                  rightParts.negative_measurable leftParts.negative_integral
                  rightParts.negative_integral]
              rfl
            negative_integral := by
              change lintegral _ (fun x => ENNReal.add
                (ENNReal.finite (NNReal.mul (leftParts.positive (first x))
                  (rightParts.negative (second x))))
                (ENNReal.finite (NNReal.mul (leftParts.negative (first x))
                  (rightParts.positive (second x))))) = _
              rw [lintegral_add _ (pairing leftParts.positive_measurable
                  rightParts.negative_measurable)
                  (pairing leftParts.negative_measurable rightParts.positive_measurable),
                lintegral_pair_mass independent leftParts.positive_measurable
                  rightParts.negative_measurable leftParts.positive_integral
                  rightParts.negative_integral,
                lintegral_pair_mass independent leftParts.negative_measurable
                  rightParts.positive_measurable leftParts.negative_integral
                  rightParts.positive_integral]
              rfl }, ?_⟩
  show Dedekind.sub (NNReal.add (NNReal.mul leftParts.positiveMass rightParts.positiveMass)
      (NNReal.mul leftParts.negativeMass rightParts.negativeMass)).toReal
    (NNReal.add (NNReal.mul leftParts.positiveMass rightParts.negativeMass)
      (NNReal.mul leftParts.negativeMass rightParts.positiveMass)).toReal = _
  rw [← leftSame, ← rightSame]
  show _ = Dedekind.mul
    (Dedekind.sub leftParts.positiveMass.toReal leftParts.negativeMass.toReal)
    (Dedekind.sub rightParts.positiveMass.toReal rightParts.negativeMass.toReal)
  rw [mul_sub_sub]
  rfl

end Pair

/-! ### Lane averages -/

/-- A value less a nonnegative one is at most the value. -/
private theorem sub_le_self_of_nonnegative {value removed : Carrier}
    (nonnegative : Dedekind.le Dedekind.zero removed) :
    Dedekind.le (Dedekind.sub value removed) value := by
  have shifted := (Dedekind.add_le_add_left_iff (shift := value)).mpr
    (Dedekind.neg_nonpositive_iff.mp nonnegative)
  rwa [Dedekind.add_zero, ← Dedekind.sub_eq_add_neg] at shifted

/-- The lane average of readings with certified means, whose distinct pairs
integrate to the product of their means, has mean square error about the
average of the means at most the share times a bound on the second moments. -/
theorem lane_variance {space : Space α} {measure : Measure space}
    (probability : Measure.IsProbability measure) {ι : Type} (lanes : Lanes ι)
    {readings : ι → α → Carrier} {means moments : ι → Carrier}
    (meanIntegral : ∀ index, HasRealIntegral measure (readings index) (means index))
    (momentIntegral : ∀ index, HasRealIntegral measure
      (fun x => Dedekind.mul (readings index x) (readings index x)) (moments index))
    (pairIntegral : ∀ first second, first ≠ second → HasRealIntegral measure
      (fun x => Dedekind.mul (readings first x) (readings second x))
      (Dedekind.mul (means first) (means second)))
    {bound : Carrier} (bounded : ∀ index, Dedekind.le (moments index) bound) :
    ∃ spread, HasRealIntegral measure (fun x =>
        Dedekind.mul
          (Dedekind.sub (lanes.realAverage fun index => readings index x)
            (lanes.realAverage means))
          (Dedekind.sub (lanes.realAverage fun index => readings index x)
            (lanes.realAverage means))) spread ∧
      Dedekind.le spread (Dedekind.mul lanes.share.toReal bound) := by
  classical
  let variance := fun index =>
    Dedekind.sub (moments index) (Dedekind.mul (means index) (means index))
  have pair : ∀ first second, HasRealIntegral measure
      (fun x => Dedekind.mul (Dedekind.sub (readings first x) (means first))
        (Dedekind.sub (readings second x) (means second)))
      (if first = second then variance first else Dedekind.zero) := by
    intro first second
    by_cases same : first = second
    · subst same
      simp only [↓reduceIte]
      exact HasRealIntegral.centred_mul probability (meanIntegral first) (meanIntegral first)
        (momentIntegral first)
    · simp only [same, ↓reduceIte]
      have cross := HasRealIntegral.centred_mul probability (meanIntegral first)
        (meanIntegral second) (pairIntegral first second same)
      rwa [Dedekind.sub_self] at cross
  have row : ∀ first, HasRealIntegral measure
      (fun x => Dedekind.additiveLaws.listSum (lanes.list.map fun second =>
        Dedekind.mul (Dedekind.sub (readings first x) (means first))
          (Dedekind.sub (readings second x) (means second)))) (variance first) := by
    intro first
    have summed := HasRealIntegral.listSum probability (pair first) lanes.list
    rw [Dedekind.additiveLaws.listSum_map_eq_single lanes.list first lanes.enumeration.nodup
      (lanes.enumeration.complete first) _
      fun _ _ different => ite_eq_right fun same => different same.symm,
      ite_eq_left rfl] at summed
    exact summed
  have rows := HasRealIntegral.listSum probability row lanes.list
  have scaled := (rows.smul lanes.share.toReal).smul lanes.share.toReal
  refine ⟨_, scaled.congr fun x => (Dedekind.listSum_centred_square lanes.list lanes.share.toReal
    (lanes.realAverage means) (fun index => readings index x) means rfl).symm, ?_⟩
  have shareNonnegative : Dedekind.le Dedekind.zero lanes.share.toReal := lanes.share.property
  have summedBound : Dedekind.le (Dedekind.additiveLaws.listSum (lanes.list.map variance))
      (Dedekind.additiveLaws.listSum (lanes.list.map fun _ => bound)) :=
    Dedekind.listSum_map_mono lanes.list _ _ fun index => Dedekind.le_trans
      (sub_le_self_of_nonnegative (Dedekind.mul_self_nonnegative (means index)))
      (bounded index)
  have inner := Dedekind.mul_le_mul_nonnegative_left summedBound shareNonnegative
  rw [show Dedekind.mul lanes.share.toReal
      (Dedekind.additiveLaws.listSum (lanes.list.map fun _ => bound)) = bound from
    lanes.realAverage_const bound] at inner
  exact Dedekind.mul_le_mul_nonnegative_left inner shareNonnegative


/-! ### Readings of weighted draws -/

section Readings

variable {space : Space α}

/-- A measurable reading of a draw's value times its weight is measurable. -/
private theorem weighted_reading_measurable {integrand : α → Carrier}
    (measurable : MeasurableMap space borel integrand) :
    MeasurableMap (Space.product space weightSpace) borel
      fun draw => Dedekind.mul (integrand draw.1) draw.2.toReal :=
  measurable_mul (MeasurableMap.comp measurable (Space.first_measurable _ _))
    (MeasurableMap.comp weight_toReal_measurable (Space.second_measurable _ _))

/-- The unnormalized estimate of a measurable reading is measurable. -/
theorem unnormalizedEstimate_measurable {ι : Type} (lanes : Lanes ι) {integrand : α → Carrier}
    (measurable : MeasurableMap space borel integrand) :
    MeasurableMap (populationSpace ι space) borel (unnormalizedEstimate lanes integrand) := by
  have terms : ∀ index, MeasurableMap (populationSpace ι space) borel fun draws =>
      Dedekind.mul (integrand (draws index).1) (draws index).2.toReal :=
    fun index => MeasurableMap.comp (weighted_reading_measurable measurable)
      (lane_measurable space index)
  have summed : ∀ entries : List ι, MeasurableMap (populationSpace ι space) borel fun draws =>
      Dedekind.additiveLaws.listSum (entries.map fun index =>
        Dedekind.mul (integrand (draws index).1) (draws index).2.toReal) := by
    intro entries
    induction entries with
    | nil => exact MeasurableMap.constant _ borel Dedekind.zero
    | cons index rest induction => exact measurable_add (terms index) induction
  intro set measurableSet
  exact measurable_mul (MeasurableMap.constant _ borel lanes.share.toReal) (summed lanes.list)
    measurableSet

/-- A reading of size at most `size` times a weight at most `bound` has size at
most `size · bound`. -/
private theorem abs_weighted_le {reading size : Carrier} {weight bound : NNReal}
    (readingBound : Dedekind.le (abs reading) size) (weightBound : NNReal.le weight bound)
    (sizeNonnegative : Dedekind.le Dedekind.zero size) :
    Dedekind.le (abs (Dedekind.mul reading weight.toReal)) (Dedekind.mul size bound.toReal) := by
  rw [abs_mul, Problib.Analysis.Real.abs_of_nonnegative (value := weight.toReal) weight.property]
  exact Dedekind.le_trans (Dedekind.mul_le_mul_nonnegative_right readingBound weight.property)
    (Dedekind.mul_le_mul_nonnegative_left weightBound sizeNonnegative)

end Readings

/-! ### Population L² laws -/

section Laws

variable {space : Space α} {result : Space β}

/-- Every lane's weight is at most `bound`, almost surely. -/
def WeightBounded {ι : Type} (population : Measure (populationSpace ι space))
    (bound : NNReal) : Prop :=
  population.AE fun draws => ∀ index, NNReal.le (draws index).2 bound

/-- The population L² law at one size: the unnormalized estimate of every
reading of size at most `size` that has an integral against the target has
mean square error at most `size² · constant / N`. -/
def EmpiricalL2 {ι : Type} (lanes : Lanes ι) (population : Measure (populationSpace ι space))
    (target : Measure space) (constant : NNReal) : Prop :=
  ∀ (size : NNReal) (integrand : α → Carrier) (value : Carrier),
    (∀ x, Dedekind.le (abs (integrand x)) size.toReal) →
    HasRealIntegral target integrand value →
    ENNReal.le (meanSquare population (unnormalizedEstimate lanes integrand) value)
      (ENNReal.finite (NNReal.mul (NNReal.mul size size) (NNReal.mul constant lanes.share)))

/-- Given the population, distinct lanes of a step are independent. -/
def PairwiseProduct {ι κ : Type}
    (step : Kernel (populationSpace ι space) (populationSpace κ result)) : Prop :=
  ∀ draws first second, first ≠ second →
    IndependentPair (step draws) (fun next => next first) (fun next => next second)
      ((step draws).map (fun next => next first) (lane_measurable result first))
      ((step draws).map (fun next => next second) (lane_measurable result second))

/-- The mean square error after a step is at most the step's conditional
variance plus the mean square error of its conditional mean. -/
theorem meanSquare_bind {source : Space γ} {population : Measure source}
    (probability : Measure.IsProbability population) {step : Kernel source result}
    (markov : population.AE fun input => Measure.IsProbability (step input)) {reading : β → Carrier}
    (measurable : MeasurableMap result borel reading) {conditional : γ → Carrier}
    (conditionalMeasurable : MeasurableMap source borel conditional)
    (mean : population.AE fun input => HasRealIntegral (step input) reading (conditional input))
    {spread : NNReal}
    (variance : population.AE fun input =>
      ENNReal.le (meanSquare (step input) reading (conditional input)) (ENNReal.finite spread))
    (value : Carrier) :
    ENNReal.le (meanSquare (population.bind step) reading value)
      (ENNReal.add (ENNReal.finite spread) (meanSquare population conditional value)) := by
  have pointwise : population.AE fun input =>
      ENNReal.le (meanSquare (step input) reading value)
        (ENNReal.add (ENNReal.finite spread) (ENNReal.ofReal (Dedekind.mul
          (Dedekind.sub (conditional input) value) (Dedekind.sub (conditional input) value)))) :=
    (markov.and (mean.and variance)).mono fun input ⟨probability, integral, below⟩ => by
      have finite := ENNReal.finite_of_le below True.intro
      have centred : MeasurableMap result borel
          (fun sample => Dedekind.sub (reading sample) (conditional input)) :=
        measurable_sub measurable (MeasurableMap.constant _ _ (conditional input))
      have spreadIntegral := hasRealIntegral_of_meanSquare (measurable_mul centred centred) finite
      rw [meanSquare_split probability integral spreadIntegral value,
        ENNReal.ofReal_toReal finite]
      exact ENNReal.add_le_add below (ENNReal.le_refl _)
  have summed := lintegral_mono_ae pointwise
  rw [lintegral_add _ (ENNRealMeasurable.constant _ _)
      (meanSquare_integrand_measurable conditionalMeasurable value),
    lintegral_const, probability.univ_eq_one, ENNReal.mul_one] at summed
  unfold meanSquare
  rw [Measure.lintegral_bind population step (meanSquare_integrand_measurable measurable value)]
  exact summed

end Laws

/-! ### Algebra of the stage constants -/

open scoped Problib.Real.AC

/-- An equation read as an order in the extended reals. -/
private theorem ennreal_le_of_eq {left right : ENNReal} (equal : left = right) :
    ENNReal.le left right :=
  equal ▸ ENNReal.le_refl left

private theorem mul_left_comm (first second third : Carrier) :
    Dedekind.mul first (Dedekind.mul second third) =
      Dedekind.mul second (Dedekind.mul first third) := by
  rw [← Dedekind.mul_assoc, Dedekind.mul_comm first second, Dedekind.mul_assoc]

/-- Two finite bounds add below a third when their reals add to it. -/
private theorem finite_add_le {first second total : NNReal}
    (equal : Dedekind.add first.toReal second.toReal = total.toReal) :
    ENNReal.le (ENNReal.add (ENNReal.finite first) (ENNReal.finite second))
      (ENNReal.finite total) := by
  show NNReal.le (NNReal.add first second) total
  exact Dedekind.le_of_equal equal

/-! ### Propagation -/

section Propagation

variable {space : Space α} {result : Space β}

/-- Propagation: continuing every lane by one weighted kernel whose weights are
at most `bound`, with pairwise independent lanes, multiplies the L² constant by
`bound²` after adding the square of the incoming weight bound. -/
theorem propagation_l2 {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)}
    (probability : Measure.IsProbability population) {target : Measure space}
    {constant weightBound bound : NNReal}
    {increment : Kernel space (Space.product result weightSpace)}
    {incrementFinite : Kernel.IsSFinite increment}
    (incrementMarkov : ∀ x, Measure.IsProbability (increment x))
    (incrementBounded : ∀ x, (increment x).AE fun draw => NNReal.le draw.2 bound)
    {step : Kernel (populationSpace ι space) (populationSpace ι result)}
    (stepMarkov : ∀ draws, Measure.IsProbability (step draws))
    (marginals : LaneMarginals step (reweight increment incrementFinite))
    (pairwise : PairwiseProduct step)
    (weights : WeightBounded population weightBound)
    (l2 : EmpiricalL2 lanes population target constant) :
    EmpiricalL2 lanes (population.bind step) (target.bind (barycenterKernel increment))
      (NNReal.mul (NNReal.mul bound bound)
        (NNReal.add constant (NNReal.mul weightBound weightBound))) := by
  intro size integrand value sized integral
  have measurable : MeasurableMap _ borel integrand := integral.measurable
  let reading := fun draw : β × NNReal => Dedekind.mul (integrand draw.1) draw.2.toReal
  have readingMeasurable : MeasurableMap (Space.product result weightSpace) borel reading :=
    weighted_reading_measurable measurable
  -- Every barycenter certifies the reading's integral.
  have fiberExists : ∀ x, ∃ fiber,
      HasRealIntegral (barycenterKernel increment x) integrand fiber := by
    intro x
    have below : ENNReal.le
        (lintegral (barycenterKernel increment x) fun y => ENNReal.ofReal (abs (integrand y)))
        (ENNReal.finite (NNReal.mul bound size)) := by
      rw [← ENNReal.finite_mul_finite, barycenterKernel_apply,
        lintegral_barycenter _ (abs_measurable measurable)]
      have constant := lintegral_mono_ae (measure := increment x)
        (right := fun _ => ENNReal.mul (ENNReal.finite bound) (ENNReal.finite size))
        ((incrementBounded x).mono fun draw light => ENNReal.mul_le_mul
          (show ENNReal.le (drawWeight draw) (ENNReal.finite bound) from light) (by
          rw [← ENNReal.ofReal_toReal_finite size]
          exact ENNReal.ofReal_monotone (sized draw.1)))
      rwa [lintegral_const, (incrementMarkov x).univ_eq_one, ENNReal.mul_one] at constant
    exact ⟨_, IntegralParts.ofSizeFinite measurable
      (ENNReal.finite_of_le below True.intro), rfl⟩
  let fiber := fun x => Classical.choose (fiberExists x)
  have fiberIntegral := fun x => Classical.choose_spec (fiberExists x)
  have weightedIntegral : ∀ x, HasRealIntegral (increment x) reading (fiber x) := fun x =>
    ProperlyWeighted.hasRealIntegral (target := barycenter (increment x)) ⟨incrementMarkov x, rfl⟩
      (fiberIntegral x)
  have fiberBound : ∀ x, Dedekind.le (abs (fiber x)) (NNReal.mul size bound).toReal := fun x =>
    HasRealIntegral.abs_le_of_ae_bounded (incrementMarkov x) (weightedIntegral x)
      (NNReal.mul size bound).property
      ((incrementBounded x).mono fun draw light => abs_weighted_le (sized draw.1) light
        size.property)
  -- The fibers integrate to the value against the incoming target.
  have fiberTarget : HasRealIntegral target fiber value := by
    have sizeFinite : ENNReal.Finite (lintegral target fun x =>
        lintegral (barycenterKernel increment x) fun y => ENNReal.ofReal (abs (integrand y))) := by
      rw [← Measure.lintegral_bind target (barycenterKernel increment)
        (abs_measurable measurable)]
      obtain ⟨parts, _⟩ := integral
      exact parts.lintegral_abs_finite
    obtain ⟨total, joint, outer⟩ :=
      Derivative.Continuous.mixture target (barycenterKernel increment) measurable sizeFinite
        fiberIntegral
    exact HasRealIntegral.unique joint integral ▸ outer
  have fiberMeasurable : MeasurableMap space borel fiber := fiberTarget.measurable
  -- One lane's law given the population.
  have laneLaw : ∀ draws index,
      (step draws).map (fun next => next index) (lane_measurable result index) =
        (increment (draws index).1).map (fun draw => (draw.1, NNReal.mul (draws index).2 draw.2))
          (scale_weight_measurable result (draws index).2) := fun draws index =>
    (marginals draws index).trans (reweight_apply increment incrementFinite (draws index))
  have laneMean : ∀ draws index, HasRealIntegral
      ((step draws).map (fun next => next index) (lane_measurable result index)) reading
      (Dedekind.mul (fiber (draws index).1) (draws index).2.toReal) := by
    intro draws index
    rw [laneLaw draws index]
    refine hasRealIntegral_map _ _ _ readingMeasurable ?_
    refine (congrArg (HasRealIntegral _ _) (Dedekind.mul_comm _ _)).mp
      (((weightedIntegral (draws index).1).smul (draws index).2.toReal).congr fun draw => ?_)
    show Dedekind.mul (draws index).2.toReal (Dedekind.mul (integrand draw.1) draw.2.toReal) =
      Dedekind.mul (integrand draw.1) (Dedekind.mul (draws index).2.toReal draw.2.toReal)
    exact mul_left_comm _ _ _
  have laneStep : ∀ draws index, HasRealIntegral (step draws) (fun next => reading (next index))
      (Dedekind.mul (fiber (draws index).1) (draws index).2.toReal) := fun draws index =>
    hasRealIntegral_of_map (step draws) (fun next => next index) (lane_measurable result index)
      (laneMean draws index)
  have conditionalMean : ∀ draws, HasRealIntegral (step draws)
      (unnormalizedEstimate lanes integrand) (unnormalizedEstimate lanes fiber draws) :=
    fun draws => (HasRealIntegral.listSum (stepMarkov draws) (laneStep draws) lanes.list).smul
      lanes.share.toReal
  -- Second moments, bounded through the incoming weight.
  let square := fun draw : β × NNReal => Dedekind.mul (reading draw) (reading draw)
  have squareMeasurable : MeasurableMap (Space.product result weightSpace) borel square :=
    measurable_mul readingMeasurable readingMeasurable
  have momentExists : ∀ (draws : ι → α × NNReal) (index : ι), ∃ moment,
      HasRealIntegral (increment (draws index).1)
      (fun draw => square (draw.1, NNReal.mul (draws index).2 draw.2)) moment :=
    fun draws index => hasRealIntegral_of_ae_bounded (incrementMarkov _)
      (MeasurableMap.comp squareMeasurable (scale_weight_measurable result (draws index).2))
      ((incrementBounded _).mono fun draw light => abs_mul_self_le_of_abs_le
        (abs_weighted_le (sized draw.1) (weight := NNReal.mul (draws index).2 draw.2)
          (bound := NNReal.mul (draws index).2 bound)
          (show NNReal.le (NNReal.mul (draws index).2 draw.2) (NNReal.mul (draws index).2 bound)
            from Dedekind.mul_le_mul_nonnegative_left light (draws index).2.property)
          size.property))
  let moment := fun draws index => Classical.choose (momentExists draws index)
  have momentIntegral := fun draws index => Classical.choose_spec (momentExists draws index)
  let peak := NNReal.mul size (NNReal.mul weightBound bound)
  have momentBound : ∀ draws index, NNReal.le (draws index).2 weightBound →
      Dedekind.le (moment draws index) (NNReal.mul peak peak).toReal := by
    intro draws index light
    refine Dedekind.le_trans (le_abs _) (HasRealIntegral.abs_le_of_ae_bounded (incrementMarkov _)
      (momentIntegral draws index) (NNReal.mul peak peak).property
      ((incrementBounded _).mono fun draw below => ?_))
    exact abs_mul_self_le_of_abs_le (abs_weighted_le (sized draw.1)
      (weight := NNReal.mul (draws index).2 draw.2) (bound := NNReal.mul weightBound bound)
      (NNReal.mul_le_mul light below) size.property)
  have momentStep : ∀ draws index, HasRealIntegral (step draws)
      (fun next => Dedekind.mul (reading (next index)) (reading (next index)))
      (moment draws index) := by
    intro draws index
    refine hasRealIntegral_of_map (step draws) (fun next => next index)
      (lane_measurable result index) (integrand := square) ?_
    rw [laneLaw draws index]
    exact hasRealIntegral_map _ _ _ squareMeasurable (momentIntegral draws index)
  have pairs : ∀ draws first second, first ≠ second → HasRealIntegral (step draws)
      (fun next => Dedekind.mul (reading (next first)) (reading (next second)))
      (Dedekind.mul (Dedekind.mul (fiber (draws first).1) (draws first).2.toReal)
        (Dedekind.mul (fiber (draws second).1) (draws second).2.toReal)) :=
    fun draws first second distinct => hasRealIntegral_pair_mul
      (pairwise draws first second distinct) (lane_measurable result first)
      (lane_measurable result second) (laneMean draws first) (laneMean draws second)
  have variance : population.AE fun draws => ENNReal.le
      (meanSquare (step draws) (unnormalizedEstimate lanes integrand)
        (unnormalizedEstimate lanes fiber draws))
      (ENNReal.finite (NNReal.mul lanes.share (NNReal.mul peak peak))) := by
    refine weights.mono fun draws light => ?_
    obtain ⟨spread, spreadIntegral, spreadBound⟩ := lane_variance (stepMarkov draws) lanes
      (readings := fun index next => reading (next index)) (laneStep draws) (momentStep draws)
      (pairs draws) (bound := (NNReal.mul peak peak).toReal)
      fun index => momentBound draws index (light index)
    have same : meanSquare (step draws) (unnormalizedEstimate lanes integrand)
        (unnormalizedEstimate lanes fiber draws) = ENNReal.ofReal spread :=
      meanSquare_eq spreadIntegral
    rw [same, ← ENNReal.ofReal_toReal_finite (NNReal.mul lanes.share (NNReal.mul peak peak))]
    exact ENNReal.ofReal_monotone spreadBound
  have bindBound := meanSquare_bind probability (Measure.ae_of_forall stepMarkov)
    (unnormalizedEstimate_measurable lanes measurable)
    (unnormalizedEstimate_measurable lanes fiberMeasurable)
    (Measure.ae_of_forall conditionalMean) variance value
  have previous := l2 (NNReal.mul size bound) fiber value fiberBound fiberTarget
  refine ENNReal.le_trans bindBound
    (ENNReal.le_trans (ENNReal.add_le_add (ENNReal.le_refl _) previous) (finite_add_le ?_))
  simp only [peak, NNReal.toReal_add, NNReal.toReal_mul, Dedekind.mul_add, Dedekind.add_mul]
  ac_rfl

/-- Propagation keeps the weights bounded by the product of the bounds. -/
theorem propagation_weight_bounded {ι : Type} (lanes : Lanes ι)
    {population : Measure (populationSpace ι space)} {weightBound bound : NNReal}
    {increment : Kernel space (Space.product result weightSpace)}
    {incrementFinite : Kernel.IsSFinite increment}
    (incrementBounded : ∀ x, (increment x).AE fun draw => NNReal.le draw.2 bound)
    {step : Kernel (populationSpace ι space) (populationSpace ι result)}
    (marginals : LaneMarginals step (reweight increment incrementFinite))
    (weights : WeightBounded population weightBound) :
    WeightBounded (population.bind step) (NNReal.mul weightBound bound) := by
  have light : ∀ index, (population.bind step).AE fun next =>
      ¬weightAbove (NNReal.mul weightBound bound) (next index) := by
    intro index
    have lightMeasurable := (populationSpace ι result).complement
      (lane_measurable result index (weightAbove_measurable result (NNReal.mul weightBound bound)))
    refine Measure.ae_bind ((populationSpace ι result).complement lightMeasurable) weights
      fun draws good => ?_
    refine (Measure.ae_map_iff (measure := step draws) (fun next => next index)
      (lane_measurable result index)
      ((Space.product result weightSpace).complement
        (weightAbove_measurable result (NNReal.mul weightBound bound)))).mp ?_
    rw [marginals draws index, reweight_apply]
    refine (Measure.ae_map_iff (measure := increment (draws index).1) _
      (scale_weight_measurable result (draws index).2)
      ((Space.product result weightSpace).complement
        (weightAbove_measurable result (NNReal.mul weightBound bound)))).mpr ?_
    exact (incrementBounded _).mono fun draw below =>
      not_weightAbove (NNReal.mul_le_mul (good index) below)
  exact (Measure.ae_forall_mem light lanes.list).mono fun next each index =>
    le_of_not_weightAbove (each index (lanes.enumeration.complete index))

/-- A lanewise map keeps the L² law with the same constant: the estimate of a
reading after the map is the estimate of the reading composed with the map
before it, against the target's image. -/
theorem lanewise_l2 {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)} {target : Measure space}
    {constant : NNReal} {map : α → β} (measurable : MeasurableMap space result map)
    (l2 : EmpiricalL2 lanes population target constant) :
    EmpiricalL2 lanes (population.map (lanewise map) (lanewise_measurable measurable))
      (target.map map measurable) constant := by
  intro size integrand value sized integral
  have below := l2 size (fun x => integrand (map x)) value (fun x => sized (map x))
    (hasRealIntegral_of_map target map measurable (integrand := integrand) integral)
  unfold meanSquare
  rw [lintegral_map _ _ _ (meanSquare_integrand_measurable
    (unnormalizedEstimate_measurable lanes integral.measurable) value)]
  exact below

/-- A lanewise map of the values keeps every weight. -/
theorem lanewise_weight_bounded {ι : Type} (lanes : Lanes ι)
    {population : Measure (populationSpace ι space)} {bound : NNReal} {map : α → β}
    (measurable : MeasurableMap space result map) (weights : WeightBounded population bound) :
    WeightBounded (population.map (lanewise map) (lanewise_measurable measurable)) bound := by
  have light : ∀ index, (population.map (lanewise map) (lanewise_measurable measurable)).AE
      fun next => ¬weightAbove bound (next index) := by
    intro index
    refine (Measure.ae_map_iff (lanewise map) (lanewise_measurable measurable)
      ((populationSpace ι result).complement
        (lane_measurable result index (weightAbove_measurable result bound)))).mpr ?_
    exact weights.mono fun _ below => not_weightAbove (below index)
  exact (Measure.ae_forall_mem light lanes.list).mono fun _ each index =>
    le_of_not_weightAbove (each index (lanes.enumeration.complete index))

end Propagation

/-! ### Resampling -/

section Resample

variable {space : Space α}

/-- At positive total weight, every child's parent is categorical, and distinct
children read their parents independently. -/
structure IndependentAncestors {ι κ : Type} (lanes : Lanes ι)
    (ancestors : Kernel (populationSpace ι space) (ancestorSpace ι κ)) : Prop where
  marginal : ∀ draws, totalWeight lanes draws ≠ NNReal.zero → ∀ child,
    (ancestors draws).map (fun parents => parents child)
        (Space.coordinate_measurable (fun _ : κ => Space.discrete ι) child) =
      categorical lanes.list fun lane => (draws lane).2
  pair : ∀ draws, totalWeight lanes draws ≠ NNReal.zero →
    ∀ first second, first ≠ second →
      IndependentPair (ancestors draws) (fun parents => parents first)
        (fun parents => parents second) (categorical lanes.list fun lane => (draws lane).2)
        (categorical lanes.list fun lane => (draws lane).2)

/-- Multinomial ancestors are independent. -/
theorem multinomial_independent {α ι : Type} {space : Space α} (lanes : Lanes ι) (count : Nat)
    [NeZero count] :
    IndependentAncestors lanes (multinomialAncestors lanes count space) where
  marginal := fun draws positive child => multinomial_marginal lanes count draws positive child
  pair := fun draws positive first second distinct function _ =>
    multinomial_pair lanes count draws positive first second distinct function

/-- A child's reading given the population: its parent's value at the mean
weight. -/
private theorem child_share {ι : Type} (lanes : Lanes ι) (draws : ι → α × NNReal)
    (positive : totalWeight lanes draws ≠ NNReal.zero) (index : ι) (value : Carrier) :
    Dedekind.mul (NNReal.div (draws index).2 (totalWeight lanes draws)).toReal
        (Dedekind.mul value (meanWeight lanes draws).toReal) =
      Dedekind.mul lanes.share.toReal (Dedekind.mul value (draws index).2.toReal) := by
  have weights : NNReal.mul (NNReal.div (draws index).2 (totalWeight lanes draws))
      (meanWeight lanes draws) = NNReal.mul lanes.share (draws index).2 := by
    rw [meanWeight_eq]
    apply NNReal.ext
    show Dedekind.mul (NNReal.div (draws index).2 (totalWeight lanes draws)).toReal
        (Dedekind.mul lanes.share.toReal (totalWeight lanes draws).toReal) =
      Dedekind.mul lanes.share.toReal (draws index).2.toReal
    rw [mul_left_comm]
    exact congrArg (Dedekind.mul lanes.share.toReal)
      (congrArg NNReal.toReal (NNReal.div_mul_cancel _ positive))
  have real := congrArg NNReal.toReal weights
  change Dedekind.mul _ (meanWeight lanes draws).toReal =
    Dedekind.mul lanes.share.toReal (draws index).2.toReal at real
  rw [mul_left_comm, real, mul_left_comm]

/-- Given the population, resampling has the unnormalized estimate as its
conditional mean, and its conditional variance is at most the share times the
square of the reading's size times the mean weight. -/
theorem resample_conditional {ι : Type} (lanes : Lanes ι)
    {ancestors : Kernel (populationSpace ι space) (ancestorSpace ι ι)}
    {ancestorsFinite : Kernel.IsSFinite ancestors}
    (ancestorsMarkov : ∀ draws, Measure.IsProbability (ancestors draws))
    (independent : IndependentAncestors lanes ancestors)
    {integrand : α → Carrier} (measurable : MeasurableMap space borel integrand)
    {size : NNReal} (sized : ∀ x, Dedekind.le (abs (integrand x)) size.toReal)
    (draws : ι → α × NNReal) :
    HasRealIntegral (resample lanes ancestors ancestorsFinite draws)
        (unnormalizedEstimate lanes integrand) (unnormalizedEstimate lanes integrand draws) ∧
      ENNReal.le (meanSquare (resample lanes ancestors ancestorsFinite draws)
          (unnormalizedEstimate lanes integrand) (unnormalizedEstimate lanes integrand draws))
        (ENNReal.finite (NNReal.mul lanes.share
          (NNReal.mul (NNReal.mul size (meanWeight lanes draws))
            (NNReal.mul size (meanWeight lanes draws))))) := by
  classical
  have estimateMeasurable : MeasurableMap (populationSpace ι space) borel
      (unnormalizedEstimate lanes integrand) :=
    unnormalizedEstimate_measurable (space := space) lanes measurable
  let copy := fun index => Dedekind.mul (integrand (draws index).1)
    (meanWeight lanes draws).toReal
  have pulled : ∀ parents : ι → ι,
      unnormalizedEstimate lanes integrand
          (fun child => ((draws (parents child)).1, meanWeight lanes draws)) =
        lanes.realAverage fun child => copy (parents child) := fun _ => rfl
  have law := resample_apply lanes ancestors ancestorsFinite draws
  by_cases zero : totalWeight lanes draws = NNReal.zero
  · -- Every weight is zero, so every reading is zero.
    have meanZero : meanWeight lanes draws = NNReal.zero := by
      rw [meanWeight_eq, zero]
      exact NNReal.ext (Dedekind.mul_zero _)
    have copyZero : ∀ index, copy index = Dedekind.zero := fun index => by
      show Dedekind.mul _ (meanWeight lanes draws).toReal = _
      rw [meanZero, NNReal.toReal_zero, Dedekind.mul_zero]
    have estimateZero : unnormalizedEstimate lanes integrand draws = Dedekind.zero := by
      show lanes.realAverage (fun index =>
        Dedekind.mul (integrand (draws index).1) (draws index).2.toReal) = _
      have each : ∀ index, Dedekind.mul (integrand (draws index).1) (draws index).2.toReal =
          Dedekind.zero := fun index => by
        rw [weight_eq_zero zero index, NNReal.toReal_zero, Dedekind.mul_zero]
      simp only [each]
      exact lanes.realAverage_const Dedekind.zero
    have pulledZero : ∀ parents : ι → ι, unnormalizedEstimate lanes integrand
        (fun child => ((draws (parents child)).1, meanWeight lanes draws)) = Dedekind.zero :=
      fun parents => by
        rw [pulled]
        simp only [copyZero]
        exact lanes.realAverage_const Dedekind.zero
    refine ⟨?_, ?_⟩
    · rw [law, estimateZero]
      refine hasRealIntegral_map _ _ _ estimateMeasurable ?_
      exact (HasRealIntegral.const (ancestorsMarkov draws) Dedekind.zero).congr
        fun parents => (pulledZero parents).symm
    · rw [law]
      unfold meanSquare
      rw [lintegral_map _ _ _ (meanSquare_integrand_measurable estimateMeasurable _)]
      have vanishes : ∀ parents : ι → ι, ENNReal.ofReal (Dedekind.mul
          (Dedekind.sub (unnormalizedEstimate lanes integrand
            (fun child => ((draws (parents child)).1, meanWeight lanes draws)))
            (unnormalizedEstimate lanes integrand draws))
          (Dedekind.sub (unnormalizedEstimate lanes integrand
            (fun child => ((draws (parents child)).1, meanWeight lanes draws)))
            (unnormalizedEstimate lanes integrand draws))) = ENNReal.zero := fun parents => by
        rw [pulledZero, estimateZero, Dedekind.sub_self, Dedekind.mul_zero, ENNReal.ofReal_zero]
      rw [lintegral_congr _ vanishes, lintegral_zero]
      exact ENNReal.zero_le _
  · -- Each child copies a categorical parent, independently of the others.
    have categoricalProbability :=
      categorical_isProbability lanes.list (weights := fun lane => (draws lane).2) zero
    have mean : Dedekind.additiveLaws.listSum (lanes.list.map (fun index => Dedekind.mul
        (NNReal.div (draws index).2 (totalWeight lanes draws)).toReal (copy index))) =
        unnormalizedEstimate lanes integrand draws := by
      show _ = Dedekind.mul lanes.share.toReal (Dedekind.additiveLaws.listSum (lanes.list.map _))
      rw [Dedekind.additiveLaws.listSum_map_hom Dedekind.additiveLaws
        (Dedekind.mul lanes.share.toReal) (Dedekind.mul_zero _) (Dedekind.mul_add _)]
      exact congrArg (fun reading => Dedekind.additiveLaws.listSum (lanes.list.map reading))
        (funext fun index => child_share lanes draws zero index (integrand (draws index).1))
    have copyIntegral := (congrArg (HasRealIntegral _ copy) mean).mp
      (hasRealIntegral_categorical lanes.list (fun lane => (draws lane).2) copy)
    have childMean : ∀ child, HasRealIntegral (ancestors draws)
        (fun parents => copy (parents child)) (unnormalizedEstimate lanes integrand draws) :=
      fun child => hasRealIntegral_of_map (ancestors draws) (fun parents => parents child)
        (Space.coordinate_measurable (fun _ : ι => Space.discrete ι) child)
        (integrand := copy) (by rw [independent.marginal draws zero child]; exact copyIntegral)
    have ancestorMean : HasRealIntegral (ancestors draws)
        (fun parents => lanes.realAverage fun child => copy (parents child))
        (unnormalizedEstimate lanes integrand draws) := by
      have summed := (HasRealIntegral.listSum (ancestorsMarkov draws) childMean lanes.list).smul
        lanes.share.toReal
      rw [show Dedekind.mul lanes.share.toReal (Dedekind.additiveLaws.listSum (lanes.list.map
          fun _ => unnormalizedEstimate lanes integrand draws)) =
        unnormalizedEstimate lanes integrand draws from lanes.realAverage_const _] at summed
      exact summed
    refine ⟨?_, ?_⟩
    · rw [law]
      exact hasRealIntegral_map _ _ _ estimateMeasurable
        (ancestorMean.congr fun parents => (pulled parents).symm)
    · let peak := NNReal.mul size (meanWeight lanes draws)
      have copyBound : ∀ index, Dedekind.le (abs (copy index)) peak.toReal := fun index =>
        abs_weighted_le (sized _) (NNReal.le_refl _) size.property
      have squareIntegral := hasRealIntegral_categorical lanes.list (fun lane => (draws lane).2)
        (fun index => Dedekind.mul (copy index) (copy index))
      have squareBound := HasRealIntegral.abs_le_of_ae_bounded categoricalProbability squareIntegral
        (NNReal.mul peak peak).property
        (Measure.ae_of_forall fun index => abs_mul_self_le_of_abs_le (copyBound index))
      have childMoment : ∀ child, HasRealIntegral (ancestors draws)
          (fun parents => Dedekind.mul (copy (parents child)) (copy (parents child))) _ :=
        fun child => hasRealIntegral_of_map (ancestors draws) (fun parents => parents child)
          (Space.coordinate_measurable (fun _ : ι => Space.discrete ι) child)
          (integrand := fun index => Dedekind.mul (copy index) (copy index))
          (by rw [independent.marginal draws zero child]; exact squareIntegral)
      have childPair : ∀ first second, first ≠ second → HasRealIntegral (ancestors draws)
          (fun parents => Dedekind.mul (copy (parents first)) (copy (parents second)))
          (Dedekind.mul (unnormalizedEstimate lanes integrand draws)
            (unnormalizedEstimate lanes integrand draws)) :=
        fun first second distinct => hasRealIntegral_pair_mul
          (independent.pair draws zero first second distinct)
          (Space.coordinate_measurable (fun _ : ι => Space.discrete ι) first)
          (Space.coordinate_measurable (fun _ : ι => Space.discrete ι) second)
          copyIntegral copyIntegral
      obtain ⟨spread, spreadIntegral, spreadBound⟩ :=
        lane_variance (ancestorsMarkov draws) lanes
        (readings := fun child parents => copy (parents child))
        (means := fun _ => unnormalizedEstimate lanes integrand draws) childMean childMoment
        childPair (bound := (NNReal.mul peak peak).toReal)
        fun _ => Dedekind.le_trans (le_abs _) squareBound
      rw [Lanes.realAverage_const] at spreadIntegral
      rw [law]
      unfold meanSquare
      rw [lintegral_map _ _ _ (meanSquare_integrand_measurable estimateMeasurable _)]
      have same : lintegral (ancestors draws) (fun parents => ENNReal.ofReal (Dedekind.mul
          (Dedekind.sub (lanes.realAverage fun child => copy (parents child))
            (unnormalizedEstimate lanes integrand draws))
          (Dedekind.sub (lanes.realAverage fun child => copy (parents child))
            (unnormalizedEstimate lanes integrand draws)))) = ENNReal.ofReal spread :=
        spreadIntegral.lintegral_ofReal fun _ => Dedekind.mul_self_nonnegative _
      refine ENNReal.le_trans (ennreal_le_of_eq same) ?_
      rw [← ENNReal.ofReal_toReal_finite (NNReal.mul lanes.share (NNReal.mul peak peak))]
      exact ENNReal.ofReal_monotone spreadBound

/-- A resampling step's L² certificate. Given the population, the step's
conditional mean square error for a measurable reading of size at most `size`
is at most `constant · share · (size · W̄)²`, where `W̄` is the mean weight. -/
def ResamplingError {ι : Type} (lanes : Lanes ι)
    (step : Kernel (populationSpace ι space) (populationSpace ι space)) (constant : NNReal) :
    Prop :=
  ∀ (draws : ι → α × NNReal) (size : NNReal) (integrand : α → Carrier),
    MeasurableMap space borel integrand →
    (∀ x, Dedekind.le (abs (integrand x)) size.toReal) →
    ENNReal.le (meanSquare (step draws) (unnormalizedEstimate lanes integrand)
        (unnormalizedEstimate lanes integrand draws))
      (ENNReal.finite (NNReal.mul constant (NNReal.mul lanes.share
        (NNReal.mul (NNReal.mul size (meanWeight lanes draws))
          (NNReal.mul size (meanWeight lanes draws))))))

/-- Independent ancestors certify resampling with constant one. -/
theorem resampling_error_of_independent {ι : Type} (lanes : Lanes ι)
    {ancestors : Kernel (populationSpace ι space) (ancestorSpace ι ι)}
    {ancestorsFinite : Kernel.IsSFinite ancestors}
    (ancestorsMarkov : ∀ draws, Measure.IsProbability (ancestors draws))
    (independent : IndependentAncestors lanes ancestors) :
    ResamplingError lanes (resample lanes ancestors ancestorsFinite) NNReal.one :=
  fun draws _ _ measurable sized => by
    rw [NNReal.one_mul]
    exact (resample_conditional lanes ancestorsMarkov independent
      (ancestorsFinite := ancestorsFinite) measurable sized draws).2

/-- Multinomial resampling is certified with constant one. -/
theorem multinomial_resampling_error {α : Type} {space : Space α} (count : Nat)
    [NeZero count] :
    ResamplingError (Lanes.fin count)
      (resample (Lanes.fin count) (multinomialAncestors (Lanes.fin count) count space)
        (multinomialFinite (Lanes.fin count) count space))
      NNReal.one :=
  resampling_error_of_independent (Lanes.fin count)
    (multinomial_markov (Lanes.fin count) count space)
    (multinomial_independent (Lanes.fin count) count)

/-- A step that keeps every population's empirical measure has the
unnormalized estimate as its conditional mean, for every measurable reading. -/
theorem resample_mean_of_invariant {ι : Type} (lanes : Lanes ι)
    {step : Kernel (populationSpace ι space) (populationSpace ι space)}
    (markov : ∀ draws, Measure.IsProbability (step draws))
    (invariant : ResampleInvariant lanes lanes step)
    {integrand : α → Carrier} (measurable : MeasurableMap space borel integrand)
    (draws : ι → α × NNReal) :
    HasRealIntegral (step draws) (unnormalizedEstimate lanes integrand)
      (unnormalizedEstimate lanes integrand draws) := by
  -- The reading has an integral against the population's empirical measure.
  have sizeFinite : ENNReal.Finite (lintegral (empirical lanes space draws)
      fun x => ENNReal.ofReal (abs (integrand x))) := by
    rw [lintegral_empirical lanes draws (abs_measurable measurable)]
    have terms : (lanes.list.map fun lane => ENNReal.mul (drawWeight (draws lane))
        (ENNReal.ofReal (abs (integrand (draws lane).1)))) =
        lanes.list.map fun lane => ENNReal.finite (NNReal.mul (draws lane).2
          (NNReal.ofReal (abs (integrand (draws lane).1)))) :=
      List.map_congr_left fun _ _ => ENNReal.finite_mul_finite _ _
    rw [terms, ← NNReal.additiveLaws.listSum_map_hom ENNReal.additiveLaws ENNReal.finite rfl
      (fun _ _ => rfl) lanes.list (fun lane => NNReal.mul (draws lane).2
        (NNReal.ofReal (abs (integrand (draws lane).1)))), ENNReal.finite_mul_finite]
    exact True.intro
  have empiricalIntegral : HasRealIntegral (empirical lanes space draws) integrand
      (IntegralParts.ofSizeFinite measurable sizeFinite).value :=
    ⟨_, rfl⟩
  -- The point mass at the population reads that integral as the estimate.
  have pointInvariant : EmpiricalInvariant lanes (empirical lanes space draws)
      (Measure.dirac (populationSpace ι space) draws) :=
    ⟨Measure.IsProbability.dirac _ draws, Measure.dirac_bind draws _⟩
  have value := (empirical_estimate_unbiased pointInvariant empiricalIntegral).unique
    (hasRealIntegral_dirac _ draws (unnormalizedEstimate_measurable lanes measurable))
  have stepInvariant : EmpiricalInvariant lanes (empirical lanes space draws) (step draws) :=
    ⟨markov draws, congrArg (fun kernel => kernel draws) invariant⟩
  rw [← value]
  exact empirical_estimate_unbiased stepInvariant empiricalIntegral

/-- A certified resampling step that keeps every empirical measure adds its
constant times the square of the weight bound to the L² constant. -/
theorem resampling_l2 {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)}
    (probability : Measure.IsProbability population) {target : Measure space}
    {previous constant weightBound : NNReal}
    {step : Kernel (populationSpace ι space) (populationSpace ι space)}
    (markov : ∀ draws, Measure.IsProbability (step draws))
    (invariant : ResampleInvariant lanes lanes step)
    (error : ResamplingError lanes step constant)
    (weights : WeightBounded population weightBound)
    (l2 : EmpiricalL2 lanes population target previous) :
    EmpiricalL2 lanes (population.bind step) target
      (NNReal.add previous (NNReal.mul constant (NNReal.mul weightBound weightBound))) := by
  intro size integrand value sized integral
  have measurable : MeasurableMap _ borel integrand := integral.measurable
  have bindBound := meanSquare_bind probability (Measure.ae_of_forall markov)
    (unnormalizedEstimate_measurable lanes measurable)
    (unnormalizedEstimate_measurable lanes measurable)
    (Measure.ae_of_forall (resample_mean_of_invariant lanes markov invariant measurable))
    (spread := NNReal.mul constant (NNReal.mul lanes.share
      (NNReal.mul (NNReal.mul size weightBound) (NNReal.mul size weightBound))))
    (weights.mono fun draws light => by
      have scaled : NNReal.le (NNReal.mul size (meanWeight lanes draws))
          (NNReal.mul size weightBound) :=
        NNReal.mul_le_mul_left (meanWeight_le lanes light) size
      refine ENNReal.le_trans (error draws size integrand measurable sized) ?_
      exact NNReal.mul_le_mul_left (NNReal.mul_le_mul_left (NNReal.mul_le_mul scaled scaled)
        lanes.share) constant)
    value
  have previousBound := l2 size integrand value sized integral
  refine ENNReal.le_trans bindBound
    (ENNReal.le_trans (ENNReal.add_le_add (ENNReal.le_refl _) previousBound) (finite_add_le ?_))
  simp only [NNReal.toReal_add, NNReal.toReal_mul, Dedekind.mul_add, Dedekind.add_mul]
  ac_rfl

/-- Resampling keeps the weights bounded: every child carries the mean
weight. -/
theorem resampling_weight_bounded {ι : Type} (lanes : Lanes ι)
    {population : Measure (populationSpace ι space)} {weightBound : NNReal}
    {ancestors : Kernel (populationSpace ι space) (ancestorSpace ι ι)}
    {ancestorsFinite : Kernel.IsSFinite ancestors}
    (weights : WeightBounded population weightBound) :
    WeightBounded (population.bind (resample lanes ancestors ancestorsFinite)) weightBound := by
  have light : ∀ index, (population.bind (resample lanes ancestors ancestorsFinite)).AE
      fun next => ¬weightAbove weightBound (next index) := by
    intro index
    have lightMeasurable := (populationSpace ι space).complement
      (lane_measurable space index (weightAbove_measurable space weightBound))
    refine Measure.ae_bind ((populationSpace ι space).complement lightMeasurable) weights
      fun draws good => ?_
    rw [resample_apply]
    refine (Measure.ae_map_iff (measure := ancestors draws) _ _
      ((populationSpace ι space).complement
        (lane_measurable space index (weightAbove_measurable space weightBound)))).mpr ?_
    exact Measure.ae_of_forall fun _ => not_weightAbove (meanWeight_le lanes good)
  exact (Measure.ae_forall_mem light lanes.list).mono fun next each index =>
    le_of_not_weightAbove (each index (lanes.enumeration.complete index))

end Resample

/-! ### The initial population -/

section Initial

variable {space : Space α}

/-- Lanes drawn independently from one properly weighted sampler whose weights
are at most `bound` satisfy the L² law with constant `bound²`. -/
theorem initial_l2 {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)}
    (probability : Measure.IsProbability population) {target : Measure space}
    {sampler : Measure (Space.product space weightSpace)} {bound : NNReal}
    (properlyWeighted : ProperlyWeighted target sampler)
    (bounded : sampler.AE fun draw => NNReal.le draw.2 bound)
    (marginals : ∀ index,
      population.map (fun draws => draws index) (lane_measurable space index) = sampler)
    (pairwise : ∀ first second, first ≠ second →
      IndependentPair population (fun draws => draws first) (fun draws => draws second)
        sampler sampler) :
    EmpiricalL2 lanes population target (NNReal.mul bound bound) := by
  intro size integrand value sized integral
  have measurable : MeasurableMap _ borel integrand := integral.measurable
  let reading := fun draw : α × NNReal => Dedekind.mul (integrand draw.1) draw.2.toReal
  have readingMeasurable : MeasurableMap (Space.product space weightSpace) borel reading :=
    weighted_reading_measurable measurable
  have weighted : HasRealIntegral sampler reading value := properlyWeighted.hasRealIntegral integral
  have laneMean : ∀ index, HasRealIntegral population
      (fun draws => reading (draws index)) value := fun index =>
    hasRealIntegral_of_map population (fun draws => draws index) (lane_measurable space index)
      (by rw [marginals index]; exact weighted)
  let peak := NNReal.mul size bound
  obtain ⟨moment, momentIntegral⟩ := hasRealIntegral_of_ae_bounded properlyWeighted.probability
    (measurable_mul readingMeasurable readingMeasurable)
    (bounded.mono fun draw light => abs_mul_self_le_of_abs_le
      (abs_weighted_le (sized draw.1) light size.property))
  have momentBound : Dedekind.le moment (NNReal.mul peak peak).toReal :=
    Dedekind.le_trans (le_abs _) (HasRealIntegral.abs_le_of_ae_bounded properlyWeighted.probability
      momentIntegral (NNReal.mul peak peak).property (bounded.mono fun draw light =>
        abs_mul_self_le_of_abs_le (abs_weighted_le (sized draw.1) light size.property)))
  have laneMoment : ∀ index, HasRealIntegral population
      (fun draws => Dedekind.mul (reading (draws index)) (reading (draws index))) moment :=
    fun index => hasRealIntegral_of_map population (fun draws => draws index)
      (lane_measurable space index)
      (integrand := fun draw => Dedekind.mul (reading draw) (reading draw))
      (by rw [marginals index]; exact momentIntegral)
  have lanePair : ∀ first second, first ≠ second → HasRealIntegral population
      (fun draws => Dedekind.mul (reading (draws first)) (reading (draws second)))
      (Dedekind.mul value value) := fun first second distinct =>
    hasRealIntegral_pair_mul (pairwise first second distinct) (lane_measurable space first)
      (lane_measurable space second) weighted weighted
  obtain ⟨spread, spreadIntegral, spreadBound⟩ := lane_variance probability lanes
    (readings := fun index draws => reading (draws index)) (means := fun _ => value)
    laneMean laneMoment lanePair (bound := (NNReal.mul peak peak).toReal) fun _ => momentBound
  rw [Lanes.realAverage_const] at spreadIntegral
  have same : meanSquare population (unnormalizedEstimate lanes integrand) value =
      ENNReal.ofReal spread := meanSquare_eq spreadIntegral
  rw [same]
  refine ENNReal.le_trans (ENNReal.ofReal_monotone spreadBound) ?_
  rw [← ENNReal.ofReal_toReal_finite (NNReal.mul (NNReal.mul size size)
    (NNReal.mul (NNReal.mul bound bound) lanes.share))]
  refine ENNReal.ofReal_monotone (Dedekind.le_of_equal ?_)
  simp only [peak, NNReal.toReal_mul, ENNReal.toReal_finite]
  ac_rfl

/-- Lanes drawn from a sampler whose weights are at most `bound` have weights at
most `bound`. -/
theorem initial_weight_bounded {ι : Type} (lanes : Lanes ι)
    {population : Measure (populationSpace ι space)}
    {sampler : Measure (Space.product space weightSpace)} {bound : NNReal}
    (bounded : sampler.AE fun draw => NNReal.le draw.2 bound)
    (marginals : ∀ index,
      population.map (fun draws => draws index) (lane_measurable space index) = sampler) :
    WeightBounded population bound := by
  have light : ∀ index, population.AE fun draws => ¬weightAbove bound (draws index) := by
    intro index
    refine (Measure.ae_map_iff (measure := population) (fun draws => draws index)
      (lane_measurable space index)
      ((Space.product space weightSpace).complement (weightAbove_measurable space bound))).mp ?_
    rw [marginals index]
    exact bounded.mono fun _ below => not_weightAbove below
  exact (Measure.ae_forall_mem light lanes.list).mono fun draws each index =>
    le_of_not_weightAbove (each index (lanes.enumeration.complete index))

end Initial

/-! ### Consistency -/

section Consistency

variable {space : Space α}

/-- Under a family of L² laws with one constant, as the lane count grows, the
unnormalized estimate of a bounded reading converges in probability to its
integral. -/
theorem estimate_consistent {ιAt : Nat → Type} (lanesAt : ∀ count, Lanes (ιAt count))
    (growing : ∀ count, (lanesAt count).count = count + 1)
    {laws : ∀ count, Measure (populationSpace (ιAt count) space)}
    {target : Measure space} {constant : NNReal}
    (l2 : ∀ count, EmpiricalL2 (lanesAt count) (laws count) target constant)
    {integrand : α → Carrier} {size : NNReal}
    (sized : ∀ x, Dedekind.le (abs (integrand x)) size.toReal)
    {value : Carrier} (integral : HasRealIntegral target integrand value) :
    ConvergesInProbability laws
      (fun count => unnormalizedEstimate (lanesAt count) integrand) value := by
  let scale := NNReal.mul (NNReal.mul size size) constant
  have bounded : ∀ count, ENNReal.le
      (meanSquare (laws count) (unnormalizedEstimate (lanesAt count) integrand) value)
      (ENNReal.finite (NNReal.mul scale (lanesAt count).share)) := by
    intro count
    have below := l2 count size integrand value sized integral
    rwa [show NNReal.mul (NNReal.mul size size) (NNReal.mul constant (lanesAt count).share) =
      NNReal.mul scale (lanesAt count).share from (NNReal.mul_assoc _ _ _).symm] at below
  have finite : ∀ count, ENNReal.Finite
      (meanSquare (laws count) (unnormalizedEstimate (lanesAt count) integrand) value) :=
    fun count => ENNReal.finite_of_le (bounded count) True.intro
  refine convergesInProbability_of_meanSquare (errors := fun count =>
    ENNReal.toReal (meanSquare (laws count) (unnormalizedEstimate (lanesAt count) integrand)
      value)) (fun count => by
        have centred : MeasurableMap (populationSpace (ιAt count) space) borel
            (fun population => Dedekind.sub
              (unnormalizedEstimate (lanesAt count) integrand population) value) := measurable_sub
          (unnormalizedEstimate_measurable (lanesAt count) integral.measurable)
          (MeasurableMap.constant _ _ value)
        exact hasRealIntegral_of_meanSquare (measurable_mul centred centred) (finite count)) ?_
  refine Problib.Analysis.Real.convergesTo_of_le_inverse scale.property
    (fun count => ENNReal.toReal_nonnegative _) fun count => ?_
  have toReal := (ENNReal.toReal_le_toReal_iff (finite count) (by exact True.intro)).mpr
    (bounded count)
  refine Dedekind.le_trans toReal (Dedekind.le_of_equal ?_)
  show Dedekind.mul scale.toReal (lanesAt count).share.toReal = _
  rw [Lanes.share, NNReal.toReal_ofRat, growing, Problib.Real.Construction.Dedekind.ofRat_inverse]
  rfl

/-- The self-normalized estimate of a bounded reading converges in probability
to the target's normalized integral, under a family of L² laws with one
constant. -/
theorem population_consistent {ιAt : Nat → Type} (lanesAt : ∀ count, Lanes (ιAt count))
    (growing : ∀ count, (lanesAt count).count = count + 1)
    {laws : ∀ count, Measure (populationSpace (ιAt count) space)}
    {target : Measure space} {constant : NNReal}
    (l2 : ∀ count, EmpiricalL2 (lanesAt count) (laws count) target constant)
    {total : Carrier} (mass : HasRealIntegral target (fun _ => Dedekind.one) total)
    (positive : total ≠ Dedekind.zero)
    {integrand : α → Carrier} {size : NNReal}
    (sized : ∀ x, Dedekind.le (abs (integrand x)) size.toReal)
    {value : Carrier} (integral : HasRealIntegral target integrand value) :
    ConvergesInProbability laws
      (fun count draws => Dedekind.div (unnormalizedEstimate (lanesAt count) integrand draws)
        (unnormalizedEstimate (lanesAt count) (fun _ => Dedekind.one) draws))
      (Dedekind.div value total) :=
  convergesInProbability_div positive
    (estimate_consistent lanesAt growing l2 sized integral)
    (estimate_consistent lanesAt growing l2 (size := NNReal.one)
      (fun _ => by
        rw [Problib.Analysis.Real.abs_of_nonnegative Dedekind.one_nonnegative]
        exact Dedekind.le_refl _) mass)

end Consistency

end Problib.Inference
