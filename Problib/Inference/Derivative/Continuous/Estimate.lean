import Problib.Inference.Derivative.Continuous.Integral
import Problib.Analysis.Real.Interchange

set_option autoImplicit false

/-! Continuous forward-mode estimator contracts.

A forward-mode estimator is a law with two readouts, a primal and a tangent.
`Estimates law primal tangent value slope` says the readouts have certified
means `value` and `slope`. `Jet objective value slope` says a real function of
one real step has value `value` and derivative `slope` at zero. An estimator is
sound for an objective when it estimates the objective's jet.

The two facts compose by different rules, so they stay separate. Estimates move
through point masses, pushforwards, and binds by the signed integral, and jets
move by the calculus. The product rule transports both at once for random
coefficients whose mixed moments with the estimator are the products of their
means. Deterministic coefficients supply those moments, and the quotient rule
uses the exact denominator jet's reciprocal as such a coefficient. The
interchange theorem of `Continuous.Interchange` turns sample derivatives into a
tangent readout.

`DirectionallyUnbiased` is the relation the RePPL appendix names between a
directional derivative and a kernel of real laws. The certified mean includes
the finite absolute first moment that the appendix states as a separate
conjunct. -/

namespace Problib.Inference.Derivative.Continuous

open Problib.Real Problib.Real.Construction.Dedekind
open Problib.Measure Problib.Measure.Real
open Problib.Analysis.Real

universe u v

variable {Outcome : Type u} {space : Space Outcome}

/-- The primal and tangent readouts of a law have the stated certified means. -/
structure Estimates (law : Measure space) (primal tangent : Outcome → selection.Carrier)
    (value slope : selection.Carrier) : Prop where
  primalMean : HasRealIntegral law primal value
  tangentMean : HasRealIntegral law tangent slope

/-- A real function of one real step has the stated value and derivative at
zero. -/
structure Jet (objective : selection.Carrier → selection.Carrier)
    (value slope : selection.Carrier) (side : Side := .two) : Prop where
  base : objective zero = value
  derivative : HasDerivativeOn side objective zero slope

namespace Jet

variable {side : Side}

/-- The product rule, with the weight's coefficients first. -/
theorem product {weight objective : selection.Carrier → selection.Carrier}
    {weightValue weightSlope value slope : selection.Carrier}
    (weightJet : Jet weight weightValue weightSlope side)
    (objectiveJet : Jet objective value slope side) :
    Jet (fun step => mul (weight step) (objective step)) (mul weightValue value)
      (add (mul weightSlope value) (mul weightValue slope)) side := by
  have derivative := hasDerivativeOn_mul weightJet.derivative objectiveJet.derivative
  rw [weightJet.base, objectiveJet.base] at derivative
  refine ⟨?_, derivative⟩
  show mul (weight zero) (objective zero) = mul weightValue value
  rw [weightJet.base, objectiveJet.base]

/-- The reciprocal of a jet whose value is not zero. -/
theorem reciprocal {denominator : selection.Carrier → selection.Carrier}
    {mass massSlope : selection.Carrier}
    (denominatorJet : Jet denominator mass massSlope side) (nonzero : mass ≠ zero) :
    Jet (fun step => inverse (denominator step)) (inverse mass)
      (neg (div massSlope (mul mass mass))) side := by
  have denominatorNonzero : denominator zero ≠ zero := by
    rw [denominatorJet.base]
    exact nonzero
  have derivative := hasDerivativeOn_inverse denominatorJet.derivative denominatorNonzero
  rw [denominatorJet.base] at derivative
  refine ⟨?_, derivative⟩
  show inverse (denominator zero) = inverse mass
  rw [denominatorJet.base]

/-- The quotient rule in coefficient form: the denominator's reciprocal jet
multiplies the numerator's jet. The denominator must not vanish at zero. -/
theorem quotient {numerator denominator : selection.Carrier → selection.Carrier}
    {value slope mass massSlope : selection.Carrier}
    (numeratorJet : Jet numerator value slope side)
    (denominatorJet : Jet denominator mass massSlope side) (nonzero : mass ≠ zero) :
    Jet (fun step => div (numerator step) (denominator step)) (mul (inverse mass) value)
      (add (mul (neg (div massSlope (mul mass mass))) value)
        (mul (inverse mass) slope)) side := by
  have product := (denominatorJet.reciprocal nonzero).product numeratorJet
  have reciprocal : (fun step => mul (inverse (denominator step)) (numerator step)) =
      fun step => div (numerator step) (denominator step) :=
    funext fun step => by rw [div_eq_mul_inverse, mul_comm]
  rwa [reciprocal] at product

end Jet

namespace Estimates

variable {side : Side}

/-- Estimates transport across pointwise equal readouts. -/
theorem congr {law : Measure space} {primal tangent primal' tangent' : Outcome → selection.Carrier}
    {value slope : selection.Carrier} (estimates : Estimates law primal tangent value slope)
    (primalEqual : ∀ outcome, primal outcome = primal' outcome)
    (tangentEqual : ∀ outcome, tangent outcome = tangent' outcome) :
    Estimates law primal' tangent' value slope :=
  ⟨estimates.primalMean.congr primalEqual, estimates.tangentMean.congr tangentEqual⟩

/-- A law estimates at most one value and one slope. -/
theorem unique {law : Measure space} {primal tangent : Outcome → selection.Carrier}
    {value slope value' slope' : selection.Carrier}
    (first : Estimates law primal tangent value slope)
    (second : Estimates law primal tangent value' slope') :
    value = value' ∧ slope = slope' :=
  ⟨first.primalMean.unique second.primalMean, first.tangentMean.unique second.tangentMean⟩

/-- A point mass estimates its readouts at the point. -/
theorem dirac (outcome : Outcome) {primal tangent : Outcome → selection.Carrier}
    (primalMeasurable : MeasurableMap space borel primal)
    (tangentMeasurable : MeasurableMap space borel tangent) :
    Estimates (Measure.dirac space outcome) primal tangent (primal outcome) (tangent outcome) :=
  ⟨hasRealIntegral_dirac space outcome primalMeasurable,
    hasRealIntegral_dirac space outcome tangentMeasurable⟩

/-- The readouts of a pushforward are the composite readouts. -/
theorem map_iff {Source : Type v} {source : Space Source} (law : Measure source)
    (before : Source → Outcome) (beforeMeasurable : MeasurableMap source space before)
    {primal tangent : Outcome → selection.Carrier} {value slope : selection.Carrier}
    (primalMeasurable : MeasurableMap space borel primal)
    (tangentMeasurable : MeasurableMap space borel tangent) :
    Estimates (law.map before beforeMeasurable) primal tangent value slope ↔
      Estimates law (fun input => primal (before input))
        (fun input => tangent (before input)) value slope :=
  ⟨fun estimates =>
      ⟨hasRealIntegral_of_map law before beforeMeasurable estimates.primalMean,
        hasRealIntegral_of_map law before beforeMeasurable estimates.tangentMean⟩,
    fun estimates =>
      ⟨hasRealIntegral_map law before beforeMeasurable primalMeasurable
          estimates.primalMean,
        hasRealIntegral_map law before beforeMeasurable tangentMeasurable
          estimates.tangentMean⟩⟩

/-- Fubini for estimates: fiber estimates at almost every input, whose means
are themselves estimated by the outer law, give estimates under the bind when
both readouts have integrable size under the iterated measure. -/
theorem bind {Source : Type v} {source : Space Source} (law : Measure source)
    (kernel : Kernel source space) {primal tangent : Outcome → selection.Carrier}
    {fiberValue fiberSlope : Source → selection.Carrier} {value slope : selection.Carrier}
    (primalMeasurable : MeasurableMap space borel primal)
    (tangentMeasurable : MeasurableMap space borel tangent)
    (primalSize : ENNReal.Finite (lintegral law (fun input =>
      lintegral (kernel input) (fun outcome => ENNReal.ofReal (abs (primal outcome))))))
    (tangentSize : ENNReal.Finite (lintegral law (fun input =>
      lintegral (kernel input) (fun outcome => ENNReal.ofReal (abs (tangent outcome))))))
    (fibers : law.AE fun input => Estimates (kernel input) primal tangent (fiberValue input)
      (fiberSlope input))
    (outer : Estimates law fiberValue fiberSlope value slope) :
    Estimates (law.bind kernel) primal tangent value slope :=
  ⟨hasRealIntegral_bind law kernel primalMeasurable primalSize
      (fibers.mono fun _ fiber => fiber.primalMean) outer.primalMean,
    hasRealIntegral_bind law kernel tangentMeasurable tangentSize
      (fibers.mono fun _ fiber => fiber.tangentMean) outer.tangentMean⟩

/-- Random coefficients act on an estimator through three mixed moments. A
coefficient readout `A` and its tangent readout `A'` share a law with an
estimator's readouts `X` and `X'`. The readouts `A·X` and `A'·X + A·X'`
estimate `a·x` and `a'·x + a·x'` when `E[A·X] = a·x`, `E[A'·X] = a'·x` and
`E[A·X'] = a·x'`. Each moment is a certified integral, so each includes its
absolute integrability. The estimator need not be unbiased for its own jet,
and coefficients independent of it supply the moments from their marginal
means. Marginal means alone do not (`Correlated`). -/
theorem jointProduct {law : Measure space}
    {coefficient coefficientTangent primal tangent : Outcome → selection.Carrier}
    {weightValue weightSlope value slope : selection.Carrier}
    (primalMoment : HasRealIntegral law
      (fun outcome => mul (coefficient outcome) (primal outcome)) (mul weightValue value))
    (slopeMoment : HasRealIntegral law
      (fun outcome => mul (coefficientTangent outcome) (primal outcome)) (mul weightSlope value))
    (tangentMoment : HasRealIntegral law
      (fun outcome => mul (coefficient outcome) (tangent outcome)) (mul weightValue slope)) :
    Estimates law (fun outcome => mul (coefficient outcome) (primal outcome))
      (fun outcome => add (mul (coefficientTangent outcome) (primal outcome))
        (mul (coefficient outcome) (tangent outcome)))
      (mul weightValue value) (add (mul weightSlope value) (mul weightValue slope)) :=
  ⟨primalMoment, slopeMoment.add tangentMoment⟩

/-- Deterministic coefficients act linearly on the two readouts: `scale`
multiplies both, and `mixing` adds a multiple of the primal to the tangent.
They are constant coefficient readouts, whose mixed moments are the scaled
means. The product and quotient rules choose the coefficients. -/
theorem linear {law : Measure space} {primal tangent : Outcome → selection.Carrier}
    {value slope : selection.Carrier} (estimates : Estimates law primal tangent value slope)
    (scale mixing : selection.Carrier) :
    Estimates law (fun outcome => mul scale (primal outcome))
      (fun outcome => add (mul mixing (primal outcome)) (mul scale (tangent outcome)))
      (mul scale value) (add (mul mixing value) (mul scale slope)) :=
  jointProduct (coefficient := fun _ => scale) (coefficientTangent := fun _ => mixing)
    (estimates.primalMean.smul scale) (estimates.primalMean.smul mixing)
    (estimates.tangentMean.smul scale)

/-- The product rule for estimators. A deterministic weight jet multiplies an
estimated objective jet, and the scaled readouts estimate the product's jet.
Random weights go through `jointProduct` with the same jets. -/
theorem product {law : Measure space} {primal tangent : Outcome → selection.Carrier}
    {weight objective : selection.Carrier → selection.Carrier}
    {weightValue weightSlope value slope : selection.Carrier}
    (estimates : Estimates law primal tangent value slope)
    (weightJet : Jet weight weightValue weightSlope side)
    (objectiveJet : Jet objective value slope side) :
    Estimates law (fun outcome => mul weightValue (primal outcome))
        (fun outcome => add (mul weightSlope (primal outcome))
          (mul weightValue (tangent outcome)))
        (mul weightValue value) (add (mul weightSlope value) (mul weightValue slope)) ∧
      Jet (fun step => mul (weight step) (objective step)) (mul weightValue value)
        (add (mul weightSlope value) (mul weightValue slope)) side :=
  ⟨estimates.linear weightValue weightSlope, weightJet.product objectiveJet⟩

/-- The quotient rule for an exact denominator jet with nonzero value. Its
reciprocal jet supplies deterministic coefficients for the estimated
numerator. A random estimator of the reciprocal jet goes through
`jointProduct` with `Jet.reciprocal` instead. Unbiased estimates of the denominator give no
unbiased reciprocal, so no rule divides one estimate by another. -/
theorem quotient {law : Measure space} {primal tangent : Outcome → selection.Carrier}
    {numerator denominator : selection.Carrier → selection.Carrier}
    {value slope mass massSlope : selection.Carrier}
    (estimates : Estimates law primal tangent value slope)
    (numeratorJet : Jet numerator value slope side)
    (denominatorJet : Jet denominator mass massSlope side) (nonzero : mass ≠ zero) :
    Estimates law (fun outcome => mul (inverse mass) (primal outcome))
        (fun outcome => add (mul (neg (div massSlope (mul mass mass))) (primal outcome))
          (mul (inverse mass) (tangent outcome)))
        (mul (inverse mass) value)
        (add (mul (neg (div massSlope (mul mass mass))) value) (mul (inverse mass) slope)) ∧
      Jet (fun step => div (numerator step) (denominator step)) (mul (inverse mass) value)
        (add (mul (neg (div massSlope (mul mass mass))) value) (mul (inverse mass) slope)) side :=
  ⟨estimates.linear (inverse mass) (neg (div massSlope (mul mass mass))),
    numeratorJet.quotient denominatorJet nonzero⟩

end Estimates

/-- The RePPL appendix's directional unbiasedness: every direction's real law
has a certified mean equal to the directional derivative in that direction. -/
def DirectionallyUnbiased {Direction : Type v} (derivative : Direction → selection.Carrier)
    (kernel : Direction → Measure borel) : Prop :=
  ∀ direction, HasRealIntegral (kernel direction) (fun sample => sample) (derivative direction)

/-- Directional unbiasedness of a second marginal is a certified mean of the
second readout of the joint law. -/
theorem directionallyUnbiased_second_iff {Direction : Type v}
    (derivative : Direction → selection.Carrier)
    (joint : Direction → Measure (Space.product space borel)) :
    DirectionallyUnbiased derivative (fun direction =>
        (joint direction).map Prod.snd (Space.second_measurable space borel)) ↔
      ∀ direction, HasRealIntegral (joint direction) (fun pair => pair.2)
        (derivative direction) := by
  constructor
  · intro unbiased direction
    exact hasRealIntegral_of_map (joint direction) Prod.snd
      (Space.second_measurable space borel) (unbiased direction)
  · intro unbiased direction
    exact hasRealIntegral_map (joint direction) Prod.snd
      (Space.second_measurable space borel) (MeasurableMap.identity borel)
      (unbiased direction)

end Problib.Inference.Derivative.Continuous
