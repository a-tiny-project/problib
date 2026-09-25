module

public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Measurable
public import Problib.Measure.Kernel.Precomp
public import Problib.Measure.Kernel.Presentation
public import Problib.Measure.Kernel.Composition.Bind
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Integral.Density.Real
public import Problib.Measure.Integral.Lebesgue.Extensionality
public import Problib.Measure.Extended.Algebra.Binary
set_option autoImplicit false

/-! Weighted draws calibrated for a measure.

A weighted draw is a value with a finite nonnegative weight. A probability law
`W` of weighted draws is calibrated for a measure `μ` when reweighting `W` by
its weights and forgetting them gives `μ` (`Calibrated`). Read on integrands,
that is `E_W[w f(x)] = ∫ f dμ` for every nonnegative measurable `f`
(`calibrated_iff_lintegral`), and the same equation holds for every real
integrand with a certified integral (`Calibrated.hasRealIntegral`). The target
may have any mass, and the expected weight is exactly that mass
(`calibrated_mass`). A law is calibrated for at most one target
(`calibrated_target_unique`), so calibration carries the target's scale and
not only its shape.

Calibrated draws compose. Continue each draw by a Markov weighted kernel and
multiply the weights, and the result is calibrated for the target bound
through the kernel's barycenters (`weighted_bind`). A kernel drawn at weight
one has itself as its barycenter (`barycenterKernel_unitWeight`), so an
adjoined auxiliary draw is one such step (`weighted_auxiliary`). Importance
sampling, unbiased estimated weights, a mapped value and an exact density
factor are single-draw stages of the same equation (`importance_weighted`,
`importance_estimated_weighted`, `weighted_map`, `weighted_density`). Draws
calibrated for a presentation's joint and returned through its return map are
calibrated for the presented kernel (`weighted_project`), which is the map
stage read at each input. -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Measure.Real (Carrier)
open Problib.Real.Construction

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

public section

/-! ### Weights -/

/-- Finite nonnegative weights, measured through their extended value. -/
abbrev weightSpace : Space NNReal := Space.comap ENNReal.finite ennrealBorel

/-- A measurable weight is measurable once read into the extended reals. -/
theorem finite_weight_measurable {space : Space α} {weight : α → NNReal}
    (measurable : MeasurableMap space weightSpace weight) :
    ENNRealMeasurable space (fun input => ENNReal.finite (weight input)) :=
  ENNRealMeasurable.of_measurableMap
    (MeasurableMap.comp (Space.comap_map ENNReal.finite ennrealBorel) measurable)

/-- A weight is measurable when its extended value is. Every measurable set of
the weight space is the preimage of one upstairs. -/
theorem weight_measurable_of_finite {space : Space α} {weight : α → NNReal}
    (embedded : ENNRealMeasurable space (fun input => ENNReal.finite (weight input))) :
    MeasurableMap space weightSpace weight := by
  intro region regionMeasurable
  obtain ⟨upstairs, upstairsMeasurable, same⟩ :=
    (Space.comap_measurable_iff ENNReal.finite ennrealBorel region).mp regionMeasurable
  rw [same]
  exact embedded.measurableMap upstairsMeasurable

/-- The product of two measurable weights is measurable. -/
theorem weight_mul_measurable {space : Space α} {left right : α → NNReal}
    (leftMeasurable : MeasurableMap space weightSpace left)
    (rightMeasurable : MeasurableMap space weightSpace right) :
    MeasurableMap space weightSpace (fun input => NNReal.mul (left input) (right input)) := by
  refine weight_measurable_of_finite ?_
  have product := ENNRealMeasurable.mul (finite_weight_measurable leftMeasurable)
    (finite_weight_measurable rightMeasurable)
  simpa only [ENNReal.finite_mul_finite] using product

/-- The weight of a weighted draw, read into the extended reals. -/
@[expose] def drawWeight (draw : α × NNReal) : ENNReal := ENNReal.finite draw.2

theorem drawWeight_measurable (space : Space α) :
    ENNRealMeasurable (Space.product space weightSpace) (drawWeight (α := α)) :=
  finite_weight_measurable (Space.second_measurable space weightSpace)

/-- Forgetting the weight of a weighted draw. -/
theorem draw_value_measurable (space : Space α) :
    MeasurableMap (Space.product space weightSpace) space Prod.fst :=
  Space.first_measurable space weightSpace

/-- The weighted integrand `w f(x)` of a measurable `f`. -/
theorem weighted_integrand_measurable {space : Space α} {function : α → ENNReal}
    (measurable : ENNRealMeasurable space function) :
    ENNRealMeasurable (Space.product space weightSpace)
      (fun draw => ENNReal.mul (drawWeight draw) (function draw.1)) :=
  ENNRealMeasurable.mul (drawWeight_measurable space)
    (measurable.comp (draw_value_measurable space))

/-! ### The calibrated equation -/

/-- Reweight a law of weighted draws by its weights, then forget the weights. -/
@[expose] noncomputable def barycenter {space : Space α}
    (weighted : Measure (Space.product space weightSpace)) : Measure space :=
  (weighted.withDensity drawWeight).map Prod.fst (draw_value_measurable space)

/-- Integrating against the barycenter weights each draw's integrand. -/
theorem lintegral_barycenter {space : Space α}
    (weighted : Measure (Space.product space weightSpace)) {function : α → ENNReal}
    (measurable : ENNRealMeasurable space function) :
    lintegral (barycenter weighted) function =
      lintegral weighted (fun draw => ENNReal.mul (drawWeight draw) (function draw.1)) := by
  rw [barycenter, lintegral_map _ _ _ measurable,
    lintegral_withDensity _ (drawWeight_measurable space)
      (measurable.comp (draw_value_measurable space))]

/-- A probability law of weighted draws whose barycenter is the target. The
target may have any mass. -/
structure Calibrated {space : Space α} (target : Measure space)
    (weighted : Measure (Space.product space weightSpace)) : Prop where
  probability : Measure.IsProbability weighted
  change : barycenter weighted = target

/-- The calibrated equation, read on a nonnegative measurable integrand. -/
theorem Calibrated.lintegral {space : Space α} {target : Measure space}
    {weighted : Measure (Space.product space weightSpace)}
    (calibrated : Calibrated target weighted) {function : α → ENNReal}
    (measurable : ENNRealMeasurable space function) :
    lintegral weighted (fun draw => ENNReal.mul (drawWeight draw) (function draw.1)) =
      lintegral target function := by
  rw [← lintegral_barycenter weighted measurable, calibrated.change]

/-- Calibration is the weighted-expectation identity for every nonnegative
measurable integrand. -/
theorem calibrated_iff_lintegral {space : Space α} {target : Measure space}
    {weighted : Measure (Space.product space weightSpace)} :
    Calibrated target weighted ↔ Measure.IsProbability weighted ∧
      ∀ function : α → ENNReal, ENNRealMeasurable space function →
        lintegral weighted (fun draw => ENNReal.mul (drawWeight draw) (function draw.1)) =
          lintegral target function := by
  constructor
  · intro calibrated
    exact ⟨calibrated.probability, fun _ measurable => calibrated.lintegral measurable⟩
  · rintro ⟨probability, equation⟩
    refine ⟨probability, (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_⟩
    rw [lintegral_barycenter weighted measurable]
    exact equation function measurable

/-- The expected weight is the target's total mass. -/
theorem calibrated_mass {space : Space α} {target : Measure space}
    {weighted : Measure (Space.product space weightSpace)}
    (calibrated : Calibrated target weighted) :
    lintegral weighted drawWeight = target Set.univ := by
  have total := calibrated.lintegral (ENNRealMeasurable.constant space ENNReal.one)
  rw [lintegral_const, ENNReal.one_mul] at total
  rw [← total]
  apply lintegral_congr
  intro draw
  exact (ENNReal.mul_one _).symm

/-- A law of weighted draws is calibrated for at most one target, so a
proportional target is a different target. -/
theorem calibrated_target_unique {space : Space α} {target other : Measure space}
    {weighted : Measure (Space.product space weightSpace)}
    (first : Calibrated target weighted) (second : Calibrated other weighted) :
    target = other :=
  first.change.symm.trans second.change

/-- The calibrated equation, read on a real integrand with a certified
integral: the integrand at the draw's value, times the draw's weight, has the
same integral under the weighted law. -/
theorem Calibrated.hasRealIntegral {space : Space α} {target : Measure space}
    {weighted : Measure (Space.product space weightSpace)}
    (calibrated : Calibrated target weighted) {integrand : α → Carrier} {value : Carrier}
    (integral : HasRealIntegral target integrand value) :
    HasRealIntegral weighted
      (fun draw => Dedekind.mul (integrand draw.1) (NNReal.toReal draw.2)) value := by
  rw [← calibrated.change] at integral
  obtain ⟨parts, same⟩ := integral
  exact HasRealIntegral.of_withDensity (density := fun draw : α × NNReal => draw.2)
    (drawWeight_measurable space) ⟨parts.comap (draw_value_measurable space), same⟩

/-! ### Weighted kernels and their composition -/

/-- The barycenter of each fiber of a weighted kernel. -/
@[expose] noncomputable def barycenterKernel {source : Space γ} {result : Space β}
    (step : Kernel source (Space.product result weightSpace)) : Kernel source result where
  toFun := fun input => barycenter (step input)
  measurable := by
    intro set setMeasurable
    have regionMeasurable := draw_value_measurable result setMeasurable
    have equal : (fun input => barycenter (step input) set) =
        fun input => lintegral (step input)
          (ennrealIndicator (Set.preimage Prod.fst set) drawWeight) := by
      funext input
      rw [barycenter, Measure.map_apply _ _ _ setMeasurable,
        Measure.withDensity_apply _ _ regionMeasurable,
        lintegral_indicator _ _ regionMeasurable]
    rw [equal]
    exact Kernel.lintegral_measurable step
      (ENNRealMeasurable.indicator regionMeasurable (drawWeight_measurable result))

theorem barycenterKernel_apply {source : Space γ} {result : Space β}
    (step : Kernel source (Space.product result weightSpace)) (input : γ) :
    barycenterKernel step input = barycenter (step input) :=
  rfl

/-- The barycenter of a bound law is the law bound through the barycenters. -/
theorem barycenter_bind {source : Space γ} {result : Space β} (measure : Measure source)
    (step : Kernel source (Space.product result weightSpace)) :
    barycenter (measure.bind step) = measure.bind (barycenterKernel step) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_barycenter _ measurable,
    Measure.lintegral_bind _ _ (weighted_integrand_measurable measurable),
    Measure.lintegral_bind _ _ measurable]
  apply lintegral_congr
  intro input
  rw [barycenterKernel_apply, lintegral_barycenter _ measurable]

/-- Multiplying a draw's weight by a fixed factor. -/
theorem scale_weight_measurable (result : Space β) (factor : NNReal) :
    MeasurableMap (Space.product result weightSpace) (Space.product result weightSpace)
      (fun draw => (draw.1, NNReal.mul factor draw.2)) :=
  Space.pair_measurable (Space.first_measurable result weightSpace)
    (weight_mul_measurable (MeasurableMap.constant _ weightSpace factor)
      (Space.second_measurable result weightSpace))

/-- The continued draw with the weights multiplied, read off an attached pair. -/
theorem reweight_pair_measurable (source : Space γ) (result : Space β) :
    MeasurableMap
      (Space.product (Space.product source weightSpace) (Space.product result weightSpace))
      (Space.product result weightSpace)
      (fun pair => (pair.2.1, NNReal.mul pair.1.2 pair.2.2)) :=
  Space.pair_measurable
    (MeasurableMap.comp (Space.first_measurable result weightSpace)
      (Space.second_measurable _ _))
    (weight_mul_measurable
      (MeasurableMap.comp (Space.second_measurable source weightSpace)
        (Space.first_measurable _ _))
      (MeasurableMap.comp (Space.second_measurable result weightSpace)
        (Space.second_measurable _ _)))

/-- Continue a weighted draw by a weighted kernel and multiply the weights. -/
@[expose] noncomputable def reweight {source : Space γ} {result : Space β}
    (step : Kernel source (Space.product result weightSpace))
    (stepFinite : Kernel.IsSFinite step) :
    Kernel (Space.product source weightSpace) (Space.product result weightSpace) :=
  ((step.precomp Prod.fst (draw_value_measurable source)).attach
      (stepFinite.precomp Prod.fst (draw_value_measurable source))).map
    (fun pair => (pair.2.1, NNReal.mul pair.1.2 pair.2.2))
    (reweight_pair_measurable source result)

theorem reweight_apply {source : Space γ} {result : Space β}
    (step : Kernel source (Space.product result weightSpace))
    (stepFinite : Kernel.IsSFinite step) (draw : γ × NNReal) :
    reweight step stepFinite draw =
      (step draw.1).map (fun value => (value.1, NNReal.mul draw.2 value.2))
        (scale_weight_measurable result draw.2) := by
  rw [reweight, Kernel.map_apply, Kernel.attach_apply, Kernel.precomp_apply, Measure.map_comp]

/-- After a reweighting step, the weighted integrand integrates to the incoming
weight times the integrand's integral against the step's barycenter. -/
theorem lintegral_reweight {source : Space γ} {result : Space β}
    (step : Kernel source (Space.product result weightSpace))
    (stepFinite : Kernel.IsSFinite step) (draw : γ × NNReal) {function : β → ENNReal}
    (measurable : ENNRealMeasurable result function) :
    lintegral (reweight step stepFinite draw)
        (fun value => ENNReal.mul (drawWeight value) (function value.1)) =
      ENNReal.mul (drawWeight draw) (lintegral (barycenterKernel step draw.1) function) := by
  have integrand := weighted_integrand_measurable measurable
  rw [reweight_apply, lintegral_map _ _ _ integrand, barycenterKernel_apply,
    lintegral_barycenter _ measurable, ← lintegral_smul _ _ integrand]
  apply lintegral_congr
  intro value
  show ENNReal.mul (ENNReal.finite (NNReal.mul draw.2 value.2)) (function value.1) =
    ENNReal.mul (ENNReal.finite draw.2)
      (ENNReal.mul (ENNReal.finite value.2) (function value.1))
  rw [← ENNReal.finite_mul_finite, ENNReal.mul_assoc]

/-- Continuing calibrated draws by a Markov weighted kernel and multiplying the
weights is calibrated for the target bound through the kernel's barycenters.
The target need not be finite. -/
theorem weighted_bind {source : Space γ} {result : Space β} {target : Measure source}
    {weighted : Measure (Space.product source weightSpace)}
    {step : Kernel source (Space.product result weightSpace)}
    (markov : ∀ input, Measure.IsProbability (step input))
    (stepFinite : Kernel.IsSFinite step) (calibrated : Calibrated target weighted) :
    Calibrated (target.bind (barycenterKernel step))
      (weighted.bind (reweight step stepFinite)) := by
  refine calibrated_iff_lintegral.mpr ⟨?_, fun function measurable => ?_⟩
  · refine calibrated.probability.bind _ fun draw => ?_
    rw [reweight_apply]
    exact (markov draw.1).map _ _
  · rw [Measure.lintegral_bind _ _ (weighted_integrand_measurable measurable),
      Measure.lintegral_bind _ _ measurable,
      ← calibrated.lintegral (Kernel.lintegral_measurable (barycenterKernel step) measurable)]
    apply lintegral_congr
    intro draw
    exact lintegral_reweight step stepFinite draw measurable

/-- A draw of weight one. -/
theorem unit_weight_measurable (result : Space β) :
    MeasurableMap result (Space.product result weightSpace)
      (fun value => (value, NNReal.one)) :=
  Space.pair_measurable (MeasurableMap.identity result)
    (MeasurableMap.constant result weightSpace NNReal.one)

/-- Draw from a kernel at weight one. -/
@[expose] noncomputable def unitWeight {source : Space γ} {result : Space β}
    (kernel : Kernel source result) : Kernel source (Space.product result weightSpace) :=
  kernel.map (fun value => (value, NNReal.one)) (unit_weight_measurable result)

theorem unitWeight_apply {source : Space γ} {result : Space β}
    (kernel : Kernel source result) (input : γ) :
    unitWeight kernel input =
      (kernel input).map (fun value => (value, NNReal.one)) (unit_weight_measurable result) :=
  rfl

/-- A unit-weight kernel is s-finite when its kernel is. -/
@[expose] noncomputable def unitWeightFinite {source : Space γ} {result : Space β}
    {kernel : Kernel source result} (kernelFinite : Kernel.IsSFinite kernel) :
    Kernel.IsSFinite (unitWeight kernel) :=
  kernelFinite.map _ (unit_weight_measurable result)

theorem unitWeight_markov {source : Space γ} {result : Space β} {kernel : Kernel source result}
    (markov : ∀ input, Measure.IsProbability (kernel input)) (input : γ) :
    Measure.IsProbability (unitWeight kernel input) :=
  (markov input).map _ (unit_weight_measurable result)

/-- A kernel drawn at weight one is its own barycenter. -/
theorem barycenterKernel_unitWeight {source : Space γ} {result : Space β}
    (kernel : Kernel source result) : barycenterKernel (unitWeight kernel) = kernel := by
  apply Kernel.ext
  intro input
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [barycenterKernel_apply, lintegral_barycenter _ measurable, unitWeight_apply,
    lintegral_map _ _ _ (weighted_integrand_measurable measurable)]
  apply lintegral_congr
  intro value
  exact ENNReal.one_mul (function value)

/-! ### Single-draw stages -/

/-- A proposal draw paired with the target's density against the proposal is
calibrated for the target. -/
theorem importance_weighted {space : Space α} {target proposal : Measure space}
    (probability : Measure.IsProbability proposal) {density : α → NNReal}
    (densityMeasurable : MeasurableMap space weightSpace density)
    (exact : target = proposal.withDensity (fun input => ENNReal.finite (density input))) :
    Calibrated target
      (proposal.map (fun input => (input, density input))
        (Space.pair_measurable (MeasurableMap.identity space) densityMeasurable)) := by
  refine calibrated_iff_lintegral.mpr ⟨probability.map _ _, fun function measurable => ?_⟩
  rw [exact, lintegral_map _ _ _ (weighted_integrand_measurable measurable),
    lintegral_withDensity _ (finite_weight_measurable densityMeasurable) measurable]
  rfl

/-- A probability kernel of finite nonnegative estimates whose mean is `mean`. -/
structure UnbiasedEstimate {space : Space α} (mean : α → ENNReal)
    (estimate : Kernel space weightSpace) : Prop where
  probability : ∀ input, Measure.IsProbability (estimate input)
  mean_eq : ∀ input, lintegral (estimate input) (fun weight => ENNReal.finite weight) = mean input

/-- The mean of an unbiased estimate is measurable. -/
theorem UnbiasedEstimate.mean_measurable {space : Space α} {mean : α → ENNReal}
    {estimate : Kernel space weightSpace} (unbiased : UnbiasedEstimate mean estimate) :
    ENNRealMeasurable space mean := by
  have equal : mean = fun input =>
      lintegral (estimate input) (fun weight => ENNReal.finite weight) :=
    funext fun input => (unbiased.mean_eq input).symm
  rw [equal]
  exact Kernel.lintegral_measurable estimate
    (finite_weight_measurable (MeasurableMap.identity weightSpace))

/-- The semiproduct of a probability measure and a Markov kernel is a
probability. -/
theorem semiproduct_isProbability {source : Space γ} {result : Space β}
    {measure : Measure source} (probability : Measure.IsProbability measure)
    {kernel : Kernel source result} (kernelFinite : Kernel.IsSFinite kernel)
    (markov : ∀ input, Measure.IsProbability (kernel input)) :
    Measure.IsProbability (measure.semiproduct kernel kernelFinite) := by
  refine probability.bind _ fun input => ?_
  rw [Kernel.attach_apply]
  exact (markov input).map _ _

/-- A proposal draw carrying an unbiased estimate of the target's density is
calibrated for the target. -/
theorem importance_estimated_weighted {space : Space α} {target proposal : Measure space}
    (probability : Measure.IsProbability proposal) {density : α → ENNReal}
    {estimate : Kernel space weightSpace} (estimateFinite : Kernel.IsSFinite estimate)
    (unbiased : UnbiasedEstimate density estimate)
    (exact : target = proposal.withDensity density) :
    Calibrated target (proposal.semiproduct estimate estimateFinite) := by
  refine calibrated_iff_lintegral.mpr
    ⟨semiproduct_isProbability probability estimateFinite unbiased.probability,
      fun function measurable => ?_⟩
  rw [lintegral_semiproduct _ _ _ (weighted_integrand_measurable measurable), exact,
    lintegral_withDensity _ unbiased.mean_measurable measurable]
  apply lintegral_congr
  intro input
  have scaled := lintegral_smul (estimate input) (function input)
    (finite_weight_measurable (MeasurableMap.identity weightSpace))
  rw [unbiased.mean_eq input] at scaled
  rw [ENNReal.mul_comm (density input), ← scaled]
  apply lintegral_congr
  intro weight
  exact ENNReal.mul_comm _ _

/-- Adjoin a draw from a kernel on the value, and keep the weight. -/
@[expose] noncomputable def adjoin {space : Space α} {extra : Space δ}
    (auxiliary : Kernel space extra) (auxiliaryFinite : Kernel.IsSFinite auxiliary) :
    Kernel (Space.product space weightSpace)
      (Space.product (Space.product space extra) weightSpace) :=
  reweight (unitWeight (auxiliary.attach auxiliaryFinite))
    (unitWeightFinite (Kernel.IsSFinite.attach auxiliaryFinite))

/-- Adjoining a Markov auxiliary draw keeps calibration, for the target joined
with the auxiliary kernel. -/
theorem weighted_auxiliary {space : Space α} {extra : Space δ} {target : Measure space}
    {weighted : Measure (Space.product space weightSpace)} {auxiliary : Kernel space extra}
    (markov : ∀ input, Measure.IsProbability (auxiliary input))
    (auxiliaryFinite : Kernel.IsSFinite auxiliary) (calibrated : Calibrated target weighted) :
    Calibrated (target.semiproduct auxiliary auxiliaryFinite)
      (weighted.bind (adjoin auxiliary auxiliaryFinite)) := by
  have attached : ∀ input, Measure.IsProbability (auxiliary.attach auxiliaryFinite input) :=
    fun input => by
      rw [Kernel.attach_apply]
      exact (markov input).map _ (Kernel.pair_left_measurable input)
  have bound := weighted_bind (unitWeight_markov attached)
    (unitWeightFinite (Kernel.IsSFinite.attach auxiliaryFinite)) calibrated
  rw [barycenterKernel_unitWeight] at bound
  exact bound

/-- The value map of a weighted draw. -/
theorem value_map_measurable {space : Space α} {result : Space β} {map : α → β}
    (measurable : MeasurableMap space result map) :
    MeasurableMap (Space.product space weightSpace) (Space.product result weightSpace)
      (fun draw => (map draw.1, draw.2)) :=
  Space.pair_measurable (MeasurableMap.comp measurable (Space.first_measurable space weightSpace))
    (Space.second_measurable space weightSpace)

/-- Mapping the value and keeping the weight is calibrated for the image
target, for any measurable map. -/
theorem weighted_map {space : Space α} {result : Space β} {target : Measure space}
    {weighted : Measure (Space.product space weightSpace)} {map : α → β}
    (measurable : MeasurableMap space result map) (calibrated : Calibrated target weighted) :
    Calibrated (target.map map measurable)
      (weighted.map (fun draw => (map draw.1, draw.2)) (value_map_measurable measurable)) := by
  refine calibrated_iff_lintegral.mpr
    ⟨calibrated.probability.map _ _, fun function functionMeasurable => ?_⟩
  rw [lintegral_map _ _ _ (weighted_integrand_measurable functionMeasurable),
    lintegral_map _ _ _ functionMeasurable,
    ← calibrated.lintegral (functionMeasurable.comp measurable)]
  rfl

/-- Returning a joint weighted draw through a jointly measurable return keeps
its weight. -/
theorem returnDraw_measurable {source : Space α} {trace : Space γ} {result : Space β}
    {ret : α × γ → β} (retMeasurable : MeasurableMap (Space.product source trace) result ret) :
    MeasurableMap (Space.product source (Space.product trace weightSpace))
      (Space.product result weightSpace) (fun draw => (ret (draw.1, draw.2.1), draw.2.2)) :=
  Space.pair_measurable
    (MeasurableMap.comp retMeasurable
      (Space.pair_measurable (Space.first_measurable source _)
        (MeasurableMap.comp (Space.first_measurable trace weightSpace)
          (Space.second_measurable source _))))
    (MeasurableMap.comp (Space.second_measurable trace weightSpace)
      (Space.second_measurable source _))

/-- Returning draws attached to their input, read at one input, is the
section's value map. -/
private theorem returned_apply {source : Space α} {trace : Space γ} {result : Space β}
    {ret : α × γ → β} (retMeasurable : MeasurableMap (Space.product source trace) result ret)
    (weighted : Kernel source (Space.product trace weightSpace))
    (weightedFinite : Kernel.IsSFinite weighted) (input : α) :
    ((weighted.attach weightedFinite).map (fun draw => (ret (draw.1, draw.2.1), draw.2.2))
        (returnDraw_measurable retMeasurable)) input =
      (weighted input).map (fun draw => (ret (input, draw.1), draw.2))
        (value_map_measurable (Kernel.section_measurable retMeasurable input)) := by
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]

/-- Draws calibrated for a presentation's joint, returned through its return
map, are calibrated for the presented kernel. -/
theorem weighted_project {source : Space α} {trace : Space γ} {result : Space β}
    {kernel : Kernel source result} {joint : Kernel source trace} {ret : α × γ → β}
    {retMeasurable : MeasurableMap (Space.product source trace) result ret}
    (presents : Kernel.Presents kernel joint ret retMeasurable)
    {weighted : Kernel source (Space.product trace weightSpace)}
    (weightedFinite : Kernel.IsSFinite weighted)
    (calibrated : ∀ input, Calibrated (joint input) (weighted input)) :
    ∀ input, Calibrated (kernel input)
      (((weighted.attach weightedFinite).map (fun draw => (ret (draw.1, draw.2.1), draw.2.2))
        (returnDraw_measurable retMeasurable)) input) := by
  intro input
  rw [returned_apply retMeasurable weighted weightedFinite input, ← presents input]
  exact weighted_map (Kernel.section_measurable retMeasurable input) (calibrated input)

/-- The same projection for draws calibrated for a positive multiple of the
joint at each input. A pushforward keeps the scale, so the multiple is
unchanged. -/
theorem weighted_project_smul {source : Space α} {trace : Space γ} {result : Space β}
    {kernel : Kernel source result} {joint : Kernel source trace} {ret : α × γ → β}
    {retMeasurable : MeasurableMap (Space.product source trace) result ret}
    (presents : Kernel.Presents kernel joint ret retMeasurable)
    {weighted : Kernel source (Space.product trace weightSpace)}
    (weightedFinite : Kernel.IsSFinite weighted) {scale : α → ENNReal}
    (calibrated : ∀ input, Calibrated (Measure.smul (scale input) (joint input)) (weighted input)) :
    ∀ input, Calibrated (Measure.smul (scale input) (kernel input))
      (((weighted.attach weightedFinite).map (fun draw => (ret (draw.1, draw.2.1), draw.2.2))
        (returnDraw_measurable retMeasurable)) input) := by
  intro input
  have mapped := weighted_map (Kernel.section_measurable retMeasurable input) (calibrated input)
  rw [Measure.map_smul, presents input] at mapped
  rw [returned_apply retMeasurable weighted weightedFinite input]
  exact mapped

/-- Multiplying each weight by the value's weight under a measurable map into
the weight space. -/
theorem density_weight_measurable {space : Space α} {density : α → NNReal}
    (densityMeasurable : MeasurableMap space weightSpace density) :
    MeasurableMap (Space.product space weightSpace) (Space.product space weightSpace)
      (fun draw => (draw.1, NNReal.mul draw.2 (density draw.1))) :=
  Space.pair_measurable (Space.first_measurable space weightSpace)
    (weight_mul_measurable (Space.second_measurable space weightSpace)
      (MeasurableMap.comp densityMeasurable (Space.first_measurable space weightSpace)))

/-- Multiplying each weight by an exact density of a new target against the
old one is calibrated for the new target. -/
theorem weighted_density {space : Space α} {reference : Measure space}
    {weighted : Measure (Space.product space weightSpace)} {density : α → NNReal}
    (densityMeasurable : MeasurableMap space weightSpace density)
    (calibrated : Calibrated reference weighted) :
    Calibrated (reference.withDensity (fun input => ENNReal.finite (density input)))
      (weighted.map (fun draw => (draw.1, NNReal.mul draw.2 (density draw.1)))
        (density_weight_measurable densityMeasurable)) := by
  refine calibrated_iff_lintegral.mpr
    ⟨calibrated.probability.map _ _, fun function measurable => ?_⟩
  have densityFinite := finite_weight_measurable densityMeasurable
  rw [lintegral_map _ _ _ (weighted_integrand_measurable measurable),
    lintegral_withDensity _ densityFinite measurable,
    ← calibrated.lintegral (ENNRealMeasurable.mul densityFinite measurable)]
  apply lintegral_congr
  intro draw
  show ENNReal.mul (ENNReal.finite (NNReal.mul draw.2 (density draw.1))) (function draw.1) =
    ENNReal.mul (ENNReal.finite draw.2)
      (ENNReal.mul (ENNReal.finite (density draw.1)) (function draw.1))
  rw [← ENNReal.finite_mul_finite, ENNReal.mul_assoc]

end

end Problib.Inference
