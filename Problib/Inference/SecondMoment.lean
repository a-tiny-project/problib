import Problib.Inference.FiniteBlock
import Problib.Measure.Kernel.Composition.Bind.Transport

set_option autoImplicit false

/-! The second-moment measure of one weighted law.

Squaring each finite nonnegative weight and taking the barycenter records the
raw second moment of every reading. The measure retains infinite integrals.
Its definition requires neither a probability law nor finite total mass.
Composition follows the ordinary weighting law after squaring both weights.
A finite signed square integral and a certified mean then give the centered
moment of the weighted reading. -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Measure.Real (Carrier)
open Problib.Real.Construction

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

section

/-- Keep the value and square the delivered weight. -/
noncomputable def squareWeight (draw : α × NNReal) : α × NNReal :=
  (draw.1, NNReal.mul draw.2 draw.2)

theorem squareWeight_measurable (space : Space α) :
    MeasurableMap (Space.product space weightSpace) (Space.product space weightSpace)
      squareWeight :=
  Space.pair_measurable (draw_value_measurable space)
    (weight_mul_measurable (Space.second_measurable space weightSpace)
      (Space.second_measurable space weightSpace))

/-- The barycenter of the same draws with their weights squared. -/
noncomputable def secondMoment {space : Space α}
    (weighted : Measure (Space.product space weightSpace)) : Measure space :=
  barycenter (weighted.map squareWeight (squareWeight_measurable space))

/-- A jointly measurable family of second-moment measures. -/
noncomputable def secondMomentKernel {source : Space γ} {result : Space α}
    (step : Kernel source (Space.product result weightSpace)) : Kernel source result :=
  barycenterKernel (step.map squareWeight (squareWeight_measurable result))

theorem secondMomentKernel_apply {source : Space γ} {result : Space α}
    (step : Kernel source (Space.product result weightSpace)) (input : γ) :
    secondMomentKernel step input = secondMoment (step input) := rfl

/-- Integrating a reading weights it by the square of the delivered weight. -/
theorem lintegral_secondMoment {space : Space α}
    (weighted : Measure (Space.product space weightSpace)) {function : α → ENNReal}
    (measurable : ENNRealMeasurable space function) :
    lintegral (secondMoment weighted) function =
      lintegral weighted (fun draw =>
        ENNReal.mul (ENNReal.mul (drawWeight draw) (drawWeight draw)) (function draw.1)) := by
  rw [secondMoment, lintegral_barycenter _ measurable,
    lintegral_map _ _ _ (weighted_integrand_measurable measurable)]
  apply lintegral_congr
  intro draw
  exact congrArg (fun weight => ENNReal.mul weight (function draw.1))
    (ENNReal.finite_mul_finite draw.2 draw.2).symm

/-- Squared draws are properly weighted for their second-moment measure. -/
theorem squared_properlyWeighted {space : Space α}
    {weighted : Measure (Space.product space weightSpace)}
    (probability : Measure.IsProbability weighted) :
    ProperlyWeighted (secondMoment weighted)
      (weighted.map squareWeight (squareWeight_measurable space)) :=
  ⟨probability.map _ _, rfl⟩

/-- A density representation of the canonical barycenter definition. -/
theorem secondMoment_eq_withDensity {space : Space α}
    (weighted : Measure (Space.product space weightSpace)) :
    secondMoment weighted =
      (weighted.withDensity (fun draw => ENNReal.finite (NNReal.mul draw.2 draw.2))).map
        Prod.fst (draw_value_measurable space) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_secondMoment _ measurable, lintegral_map _ _ _ measurable,
    lintegral_withDensity _
      (finite_weight_measurable (weight_mul_measurable
        (Space.second_measurable space weightSpace) (Space.second_measurable space weightSpace)))
      (measurable.comp (draw_value_measurable space))]
  apply lintegral_congr
  intro draw
  simp only [drawWeight, ENNReal.finite_mul_finite]

private theorem square_mul (left right : NNReal) :
    NNReal.mul (NNReal.mul left right) (NNReal.mul left right) =
      NNReal.mul (NNReal.mul left left) (NNReal.mul right right) := by
  apply NNReal.ext
  simp only [NNReal.toReal_mul]
  exact Dedekind.mul_mul_mul_comm _ _ _ _

/-- Squaring a continued draw squares both incoming and continuation weights. -/
theorem squareWeight_reweight {source : Space γ} {result : Space β}
    (step : Kernel source (Space.product result weightSpace))
    (stepFinite : Kernel.IsSFinite step) (draw : γ × NNReal) :
    (reweight step stepFinite draw).map squareWeight (squareWeight_measurable result) =
      reweight (step.map squareWeight (squareWeight_measurable result))
        (stepFinite.map squareWeight (squareWeight_measurable result)) (squareWeight draw) := by
  rw [reweight_apply, reweight_apply, Kernel.map_apply, Measure.map_comp, Measure.map_comp]
  have same : (fun value : β × NNReal =>
      squareWeight (value.1, NNReal.mul draw.2 value.2)) =
      (fun value : β × NNReal =>
        ((squareWeight value).1, NNReal.mul (squareWeight draw).2 (squareWeight value).2)) := by
    funext value
    exact congrArg (fun weight => (value.1, weight)) (square_mul draw.2 value.2)
  apply Measure.ext
  intro region measurable
  rw [Measure.map_apply _ _ _ measurable, Measure.map_apply _ _ _ measurable]
  exact congrArg (fun function => (step draw.1) (Set.preimage function region)) same

/-- The squared law of a weighted bind is the bind of the squared laws. -/
theorem squareWeight_bind {source : Space γ} {result : Space β}
    (weighted : Measure (Space.product source weightSpace))
    (step : Kernel source (Space.product result weightSpace))
    (stepFinite : Kernel.IsSFinite step) :
    (weighted.bind (reweight step stepFinite)).map squareWeight (squareWeight_measurable result) =
      (weighted.map squareWeight (squareWeight_measurable source)).bind
        (reweight (step.map squareWeight (squareWeight_measurable result))
          (stepFinite.map squareWeight (squareWeight_measurable result))) := by
  rw [Measure.map_bind, Measure.bind_map]
  congr 1
  apply Kernel.ext
  intro draw
  exact squareWeight_reweight step stepFinite draw

/-- Composition conditions on the first value. The continuation cannot read
its weight. Conditional second moments may depend on that value. -/
theorem secondMoment_weighted_bind {source : Space γ} {result : Space β}
    {weighted : Measure (Space.product source weightSpace)}
    {step : Kernel source (Space.product result weightSpace)}
    (probability : Measure.IsProbability weighted)
    (markov : ∀ input, Measure.IsProbability (step input))
    (stepFinite : Kernel.IsSFinite step) :
    secondMoment (weighted.bind (reweight step stepFinite)) =
      (secondMoment weighted).bind (secondMomentKernel step) := by
  have composed := weighted_bind
    (fun input => (markov input).map squareWeight (squareWeight_measurable result))
    (stepFinite.map squareWeight (squareWeight_measurable result))
    (squared_properlyWeighted probability)
  rw [secondMoment, squareWeight_bind]
  exact composed.change

/-- Mapping values and keeping their weights pushes the moment measure forward. -/
theorem secondMoment_weighted_map {space : Space α} {result : Space β}
    (weighted : Measure (Space.product space weightSpace)) {map : α → β}
    (measurable : MeasurableMap space result map) :
    secondMoment (weighted.map (fun draw => (map draw.1, draw.2))
      (value_map_measurable measurable)) = (secondMoment weighted).map map measurable := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function functionMeasurable => ?_
  rw [lintegral_secondMoment _ functionMeasurable,
    lintegral_map _ _ _ ((drawWeight_measurable result).mul
      (drawWeight_measurable result) |>.mul (functionMeasurable.comp (draw_value_measurable result))),
    lintegral_map _ _ _ functionMeasurable,
    lintegral_secondMoment _ (functionMeasurable.comp measurable)]
  rfl

/-- A factor on each weight becomes its square on the moment measure. -/
theorem secondMoment_weighted_density {space : Space α}
    (weighted : Measure (Space.product space weightSpace)) {density : α → NNReal}
    (densityMeasurable : MeasurableMap space weightSpace density) :
    secondMoment (weighted.map (fun draw => (draw.1, NNReal.mul draw.2 (density draw.1)))
      (density_weight_measurable densityMeasurable)) =
      (secondMoment weighted).withDensity
        (fun input => ENNReal.finite (NNReal.mul (density input) (density input))) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have squareMeasurable := finite_weight_measurable
    (weight_mul_measurable densityMeasurable densityMeasurable)
  rw [lintegral_secondMoment _ measurable,
    lintegral_map _ _ _ ((drawWeight_measurable space).mul
      (drawWeight_measurable space) |>.mul (measurable.comp (draw_value_measurable space))),
    lintegral_withDensity _ squareMeasurable measurable,
    lintegral_secondMoment _ (squareMeasurable.mul measurable)]
  apply lintegral_congr
  intro draw
  show ENNReal.mul
      (ENNReal.mul (ENNReal.finite (NNReal.mul draw.2 (density draw.1)))
        (ENNReal.finite (NNReal.mul draw.2 (density draw.1)))) (function draw.1) = _
  rw [ENNReal.finite_mul_finite, square_mul, ← ENNReal.finite_mul_finite,
    ← ENNReal.finite_mul_finite, ENNReal.mul_assoc]
  simp only [drawWeight, ENNReal.finite_mul_finite]

/-- Constant weight scaling squares the scale of the moment measure. -/
theorem secondMoment_scale {space : Space α}
    (weighted : Measure (Space.product space weightSpace)) (factor : NNReal) :
    secondMoment (weighted.map (fun draw => (draw.1, NNReal.mul factor draw.2))
      (scale_weight_measurable space factor)) =
      Measure.smul (ENNReal.finite (NNReal.mul factor factor)) (secondMoment weighted) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_secondMoment _ measurable,
    lintegral_map _ _ _ ((drawWeight_measurable space).mul
      (drawWeight_measurable space) |>.mul (measurable.comp (draw_value_measurable space))),
    lintegral_smul_measure, lintegral_secondMoment _ measurable,
    ← lintegral_smul weighted _ ((drawWeight_measurable space).mul
      (drawWeight_measurable space) |>.mul (measurable.comp (draw_value_measurable space)))]
  apply lintegral_congr
  intro draw
  show ENNReal.mul
      (ENNReal.mul (ENNReal.finite (NNReal.mul factor draw.2))
        (ENNReal.finite (NNReal.mul factor draw.2))) (function draw.1) = _
  rw [ENNReal.finite_mul_finite, square_mul, ← ENNReal.finite_mul_finite,
    ← ENNReal.finite_mul_finite, ENNReal.mul_assoc]
  simp only [drawWeight, ENNReal.finite_mul_finite]

/-- Constant-weight draws have the original measure scaled by the square. -/
theorem secondMoment_constantWeight {space : Space α}
    (measure : Measure space) (weight : NNReal) :
    secondMoment (measure.map (fun value => (value, weight))
      (Space.pair_measurable (MeasurableMap.identity space)
        (MeasurableMap.constant space weightSpace weight))) =
      Measure.smul (ENNReal.finite (NNReal.mul weight weight)) measure := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_secondMoment _ measurable,
    lintegral_map _ _ _ ((drawWeight_measurable space).mul
      (drawWeight_measurable space) |>.mul (measurable.comp (draw_value_measurable space))),
    lintegral_smul_measure]
  simpa only [drawWeight, ENNReal.finite_mul_finite] using
    lintegral_smul measure (ENNReal.finite (NNReal.mul weight weight)) measurable

/-- Unit weights keep the original measure. -/
theorem secondMoment_unitWeight {space : Space α} (measure : Measure space) :
    secondMoment (measure.map (fun value => (value, NNReal.one)) (unit_weight_measurable space)) =
      measure := by
  rw [secondMoment_constantWeight, NNReal.mul_one]
  exact Measure.one_smul measure

/-- Exact normalized draws at mass Z have moment measure Z times the target,
including zero mass with any fallback measure. -/
theorem secondMoment_exactBlock {space : Space α} {target sampler : Measure space}
    (mass : NNReal)
    (total : target Set.univ = ENNReal.finite mass)
    (conditional : ∀ nonzero : mass ≠ NNReal.zero,
      sampler = Measure.normalize target (Measure.IsNormalizable.of_finite_mass total nonzero)) :
    secondMoment (sampler.map (fun value => (value, mass))
      (Space.pair_measurable (MeasurableMap.identity space)
        (MeasurableMap.constant space weightSpace mass))) =
      Measure.smul (ENNReal.finite mass) target := by
  have reconstruct : Measure.smul (ENNReal.finite mass) sampler = target := by
    by_cases zero : mass = NNReal.zero
    · have targetZero := (Measure.eq_zero_iff_univ_eq_zero target).mpr
        (total.trans (congrArg ENNReal.finite zero))
      rw [zero, targetZero]
      exact Measure.zero_smul sampler
    · rw [conditional zero, ← total]
      exact Measure.smul_normalize _ _
  rw [secondMoment_constantWeight, ← reconstruct, Measure.smul_smul, ENNReal.finite_mul_finite]

/-- The exact-block identity read at one input. -/
theorem secondMoment_blockDraw {source : Space γ} {result : Space α}
    (target sampler : Kernel source result)
    (markov : ∀ input, Measure.IsProbability (sampler input))
    (mass : γ → NNReal) (massMeasurable : MeasurableMap source weightSpace mass)
    (total : ∀ input, target input Set.univ = ENNReal.finite (mass input))
    (conditional : ∀ input, ∀ nonzero : mass input ≠ NNReal.zero,
      sampler input = Measure.normalize (target input)
        (Measure.IsNormalizable.of_finite_mass (total input) nonzero)) (input : γ) :
    secondMoment (blockDraw sampler markov mass massMeasurable input) =
      Measure.smul (ENNReal.finite (mass input)) (target input) := by
  rw [blockDraw_apply]
  exact secondMoment_exactBlock (mass input) (total input) (conditional input)

/-- Deterministic importance draws have density equal to the density squared. -/
theorem secondMoment_importance {space : Space α} (proposal : Measure space)
    {density : α → NNReal} (densityMeasurable : MeasurableMap space weightSpace density) :
    secondMoment (proposal.map (fun input => (input, density input))
      (Space.pair_measurable (MeasurableMap.identity space) densityMeasurable)) =
      proposal.withDensity (fun input => ENNReal.finite (NNReal.mul (density input) (density input))) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_secondMoment _ measurable,
    lintegral_map _ _ _ ((drawWeight_measurable space).mul
      (drawWeight_measurable space) |>.mul (measurable.comp (draw_value_measurable space))),
    lintegral_withDensity _
      (finite_weight_measurable (weight_mul_measurable densityMeasurable densityMeasurable)) measurable]
  apply lintegral_congr
  intro input
  simp only [drawWeight, ENNReal.finite_mul_finite]

/-- Reweighting the deterministic importance target once more gives its moment
measure. Random unbiased estimates require their own second-moment law. -/
theorem secondMoment_importance_target {space : Space α} {target proposal : Measure space}
    {density : α → NNReal} (densityMeasurable : MeasurableMap space weightSpace density)
    (exact : target = proposal.withDensity (fun input => ENNReal.finite (density input))) :
    secondMoment (proposal.map (fun input => (input, density input))
      (Space.pair_measurable (MeasurableMap.identity space) densityMeasurable)) =
      target.withDensity (fun input => ENNReal.finite (density input)) := by
  rw [secondMoment_importance _ densityMeasurable, exact,
    Measure.withDensity_withDensity _ (finite_weight_measurable densityMeasurable)
      (finite_weight_measurable densityMeasurable)]
  simp only [ENNReal.finite_mul_finite]

/-- A finite signed square integral transfers to the square of the weighted
reading. The certified mean supplies measurability at the centered bridge. -/
theorem secondMoment_hasRealIntegral {space : Space α}
    {weighted : Measure (Space.product space weightSpace)} {function : α → Carrier} {value : Carrier}
    (integral : HasRealIntegral (secondMoment weighted)
      (fun input => Dedekind.mul (function input) (function input)) value) :
    HasRealIntegral weighted (fun draw =>
      Dedekind.mul (Dedekind.mul (function draw.1) (NNReal.toReal draw.2))
        (Dedekind.mul (function draw.1) (NNReal.toReal draw.2))) value := by
  rw [secondMoment_eq_withDensity] at integral
  obtain ⟨parts, same⟩ := integral
  have pulled := HasRealIntegral.of_withDensity
    (density := fun draw : α × NNReal => NNReal.mul draw.2 draw.2)
    (finite_weight_measurable (weight_mul_measurable
      (Space.second_measurable space weightSpace) (Space.second_measurable space weightSpace)))
    (show HasRealIntegral _ _ value from ⟨parts.comap (draw_value_measurable space), same⟩)
  refine pulled.congr fun draw => ?_
  rw [NNReal.toReal_mul]
  exact Dedekind.mul_mul_mul_comm _ _ _ _

/-- A certified mean and finite raw second moment give the centered moment.
No bound on the total mass of the moment measure is required. -/
theorem centered_of_secondMoment {space : Space α} {target : Measure space}
    {weighted : Measure (Space.product space weightSpace)}
    (properlyWeighted : ProperlyWeighted target weighted) {function : α → Carrier} {mean raw : Carrier}
    (meanIntegral : HasRealIntegral target function mean)
    (squareIntegral : HasRealIntegral (secondMoment weighted)
      (fun input => Dedekind.mul (function input) (function input)) raw) :
    HasRealIntegral weighted (fun draw =>
      Dedekind.mul (Dedekind.sub (Dedekind.mul (function draw.1) (NNReal.toReal draw.2)) mean)
        (Dedekind.sub (Dedekind.mul (function draw.1) (NNReal.toReal draw.2)) mean))
      (Dedekind.sub raw (Dedekind.mul mean mean)) :=
  HasRealIntegral.centred_mul properlyWeighted.probability
    (properlyWeighted.hasRealIntegral meanIntegral) (properlyWeighted.hasRealIntegral meanIntegral)
    (secondMoment_hasRealIntegral squareIntegral)

end

end Problib.Inference
