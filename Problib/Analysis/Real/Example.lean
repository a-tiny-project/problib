module

public import Problib.Analysis.Real.Interchange
public import Problib.Analysis.Gaussian.Conjugate

/-! The canary: the conjugate posterior mean differentiated in the prior mean.

The scalar normal-normal posterior mean is affine in the prior mean with slope
the likelihood variance over the total variance, so it is the smallest honest
test that the calculus above composes: a constant, an identity, a scalar
multiple, and a sum, over four runtime parameters of which three are held
fixed. The directional form runs the same fact through the four-parameter
subtype-of-products space the model actually uses, which is where a wrong
projection or a wrong line would show up.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

/-- The posterior mean is affine in the prior mean with slope the likelihood
variance over the total variance. -/
public theorem posteriorMean_derivative
    (observation priorMean priorVariance likelihoodVariance : selection.Carrier)
    (priorPositive : lt zero priorVariance)
    (likelihoodPositive : lt zero likelihoodVariance) :
    HasDerivative
      (fun mean =>
        Gaussian.posteriorMean observation mean priorVariance likelihoodVariance)
      priorMean
      (div likelihoodVariance (add priorVariance likelihoodVariance)) := by
  have totalPositive : lt zero (add priorVariance likelihoodVariance) :=
    add_positive priorPositive likelihoodPositive
  have totalNonzero : add priorVariance likelihoodVariance ≠ zero := by
    intro vanished
    have copy := totalPositive
    rw [vanished] at copy
    exact lt_irrefl zero copy
  have affine := hasDerivative_smul
    (inverse (add priorVariance likelihoodVariance))
    (hasDerivative_add
      (hasDerivative_const (mul priorVariance observation) priorMean)
      (hasDerivative_smul likelihoodVariance (hasDerivative_identity priorMean)))
  have functionForm :
      (fun mean => mul (inverse (add priorVariance likelihoodVariance))
          (add (mul priorVariance observation) (mul likelihoodVariance mean))) =
        fun mean =>
          Gaussian.posteriorMean observation mean priorVariance
            likelihoodVariance := by
    funext mean
    simp only [Gaussian.posteriorMean, div_eq_mul_inverse]
    rw [mul_comm]
  have derivativeForm :
      mul (inverse (add priorVariance likelihoodVariance))
          (add zero (mul likelihoodVariance one)) =
        div likelihoodVariance (add priorVariance likelihoodVariance) := by
    rw [mul_one, add_comm zero likelihoodVariance, add_zero, div_eq_mul_inverse, mul_comm]
  rw [functionForm, derivativeForm] at affine
  exact affine

/-! ### The four-parameter space

Observation, prior mean, prior variance, likelihood variance, with both
variances positive. The shape is the one the model registers at runtime: a
product of products cut down by a subtype. -/

/-- The M7 parameter space. -/
public abbrev Parameters :=
  { tuple : (selection.Carrier × selection.Carrier) ×
      (selection.Carrier × selection.Carrier) //
    lt zero tuple.2.1 ∧ lt zero tuple.2.2 }

/-- The posterior mean read off the packed parameter space. -/
@[expose] public noncomputable def packedPosteriorMean
    (parameters : Parameters) : selection.Carrier :=
  Gaussian.posteriorMean parameters.val.1.1 parameters.val.1.2
    parameters.val.2.1 parameters.val.2.2

/-- The line through the parameter point that moves only the prior mean. -/
@[expose] public noncomputable def priorMeanLine
    (observation priorMean priorVariance likelihoodVariance : selection.Carrier)
    (priorPositive : lt zero priorVariance)
    (likelihoodPositive : lt zero likelihoodVariance) :
    selection.Carrier → Parameters :=
  lineSubtype
    (lineProduct
      (lineProduct (lineConst observation) (line priorMean one))
      (lineConst (priorVariance, likelihoodVariance)))
    (fun _ => ⟨priorPositive, likelihoodPositive⟩)

/-- The canary: along the prior-mean line of the four-parameter space, the
posterior mean has the closed-form sensitivity. -/
public theorem packedPosteriorMean_directional
    (observation priorMean priorVariance likelihoodVariance : selection.Carrier)
    (priorPositive : lt zero priorVariance)
    (likelihoodPositive : lt zero likelihoodVariance) :
    HasDirectionalDerivative packedPosteriorMean
      (priorMeanLine observation priorMean priorVariance likelihoodVariance
        priorPositive likelihoodPositive)
      (div likelihoodVariance (add priorVariance likelihoodVariance)) :=
  hasDirectionalDerivative_line.mpr
    (posteriorMean_derivative observation priorMean priorVariance
      likelihoodVariance priorPositive likelihoodPositive)

end

end Problib.Analysis.Real
