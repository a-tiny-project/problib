module

public import Problib.Analysis.Gaussian.Density
public import Problib.Analysis.Exponential.Derivative
public import Problib.Analysis.Pi
public import Problib.Analysis.Real.Directional

/-! The Gaussian density along a curve in its three arguments.

At positive variance the normalizer is the exponential of half the logarithm of
`2 * pi * variance`, so the density is the exponential of one log density,
`-(value - mean)^2 / (2 variance) - log (2 pi variance) / 2`. When the mean, the
variance, and the value move along differentiable curves, the log density
differentiates by the quotient, reciprocal, and logarithm rules, and the density
by the chain rule through `hasDerivative_exp`. The slope depends only on the
centered value, the variance, and their rates. The mean, variance, and value
derivatives are its coordinate cases, and a line in any direction of the three
is one curve.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real Logarithm

noncomputable section

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩
private instance : Std.Commutative (α := selection.Carrier) mul := ⟨mul_comm⟩
private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩
private instance : Std.Commutative (α := selection.Carrier) add := ⟨add_comm⟩

/-- A difference of a difference is one difference. -/
private theorem sub_sub_add (first second third : selection.Carrier) :
    sub (sub first second) third = sub first (add second third) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, add_assoc]

/-! ### The log density -/

/-- The logarithm of the density at positive variance. -/
@[expose] public def logDensity (mean variance value : selection.Carrier) : selection.Carrier :=
  sub (neg (div (mul (sub value mean) (sub value mean)) (mul (selection.ofRat 2) variance)))
    (div (logIntegral (mul (mul (selection.ofRat 2) pi) variance)) (add one one))

/-- At positive variance the density is the exponential of its log density. -/
public theorem density_exp (mean variance value : selection.Carrier)
    (positive : lt zero variance) :
    (density mean variance value).toReal = exp (logDensity mean variance value) := by
  have scaledPositive : lt zero (mul (mul (selection.ofRat 2) pi) variance) :=
    mul_positive (mul_positive ofRat_two_positive pi_positive) positive
  have embedded : (NNReal.ofReal (mul (mul (selection.ofRat 2) pi) variance)).val =
      mul (mul (selection.ofRat 2) pi) variance :=
    NNReal.toReal_ofReal (le_of_lt scaledPositive)
  have normalizerForm : (normalizer variance).toReal =
      exp (div (logIntegral (mul (mul (selection.ofRat 2) pi) variance)) (add one one)) := by
    unfold normalizer
    rw [sqrt_of_positive _ (by
      change lt zero (NNReal.toReal (NNReal.ofReal _))
      rw [NNReal.toReal_ofReal (le_of_lt scaledPositive)]
      exact scaledPositive), embedded]
    exact NNReal.toReal_ofReal (le_of_lt (exp_positive _))
  rw [density_toReal, normalizerForm, div_eq_mul_inverse, ← exp_neg, ← exp_add, ← sub_eq_add_neg]
  rfl

/-- The slope of the log density along a curve, from the centered value, the
variance, and their rates. -/
@[expose] public def logDensitySlope (centered variance centeredRate varianceRate : selection.Carrier) :
    selection.Carrier :=
  sub (div (mul (mul centered centered) varianceRate)
      (mul (selection.ofRat 2) (mul variance variance)))
    (add (div (mul centered centeredRate) variance)
      (div varianceRate (mul (selection.ofRat 2) variance)))

/-- The scaled square of a curve over twice a curve of nonzero value. -/
private theorem hasDerivative_quadratic {centered variance : selection.Carrier → selection.Carrier}
    {point centeredRate varianceRate : selection.Carrier}
    (centeredDifferentiable : HasDerivative centered point centeredRate)
    (varianceDifferentiable : HasDerivative variance point varianceRate)
    (nonzero : variance point ≠ zero) :
    HasDerivative
      (fun step => div (mul (centered step) (centered step))
        (mul (selection.ofRat 2) (variance step))) point
      (sub (div (mul (centered point) centeredRate) (variance point))
        (div (mul (mul (centered point) (centered point)) varianceRate)
          (mul (selection.ofRat 2) (mul (variance point) (variance point))))) := by
  have square := hasDerivative_mul centeredDifferentiable centeredDifferentiable
  have reciprocal := hasDerivative_inverse varianceDifferentiable nonzero
  have product := hasDerivative_mul square reciprocal
  have scaled := hasDerivative_smul (inverse (selection.ofRat 2)) product
  have functionEqual : (fun step => mul (inverse (selection.ofRat 2))
      (mul (mul (centered step) (centered step)) (inverse (variance step)))) =
      (fun step => div (mul (centered step) (centered step))
        (mul (selection.ofRat 2) (variance step))) := by
    funext step
    rw [div_eq_mul_inverse, inverse_mul_total]
    ac_rfl
  have doubled : add (mul centeredRate (centered point)) (mul (centered point) centeredRate) =
      mul (mul (centered point) centeredRate) (selection.ofRat 2) := by
    rw [mul_comm centeredRate (centered point), add_self]
    rfl
  rw [functionEqual, doubled] at scaled
  have derivativeEqual :
      mul (inverse (selection.ofRat 2))
        (add (mul (mul (mul (centered point) centeredRate) (selection.ofRat 2))
            (inverse (variance point)))
          (mul (mul (centered point) (centered point))
            (neg (div varianceRate (mul (variance point) (variance point)))))) =
      sub (div (mul (centered point) centeredRate) (variance point))
        (div (mul (mul (centered point) (centered point)) varianceRate)
          (mul (selection.ofRat 2) (mul (variance point) (variance point)))) := by
    rw [mul_add, mul_neg, mul_neg, sub_eq_add_neg, div_eq_mul_inverse, div_eq_mul_inverse, div_eq_mul_inverse,
      inverse_mul_total (selection.ofRat 2)]
    congr 1
    · calc mul (inverse (selection.ofRat 2))
            (mul (mul (mul (centered point) centeredRate) (selection.ofRat 2))
              (inverse (variance point)))
          = mul (mul (mul (centered point) centeredRate) (inverse (variance point)))
              (mul (inverse (selection.ofRat 2)) (selection.ofRat 2)) := by ac_rfl
        _ = _ := by rw [inverse_mul_cancel ofRat_two_nonzero, mul_one]
    · congr 1
      ac_rfl
  rwa [derivativeEqual] at scaled

/-- Half the logarithm of `2 * pi` times a positive curve. -/
private theorem hasDerivative_half_log {variance : selection.Carrier → selection.Carrier}
    {point varianceRate : selection.Carrier}
    (varianceDifferentiable : HasDerivative variance point varianceRate)
    (positive : lt zero (variance point)) :
    HasDerivative
      (fun step => div (logIntegral (mul (mul (selection.ofRat 2) pi) (variance step)))
        (add one one)) point
      (div varianceRate (mul (selection.ofRat 2) (variance point))) := by
  have constantPositive : lt zero (mul (selection.ofRat 2) pi) :=
    mul_positive ofRat_two_positive pi_positive
  have scaled := hasDerivative_smul (mul (selection.ofRat 2) pi) varianceDifferentiable
  have logarithm := hasDerivative_comp (outer := logIntegral)
    (inner := fun step => mul (mul (selection.ofRat 2) pi) (variance step))
    (hasDerivative_log (mul_positive constantPositive positive)) scaled
  have halved := hasDerivative_smul (inverse (add one one)) logarithm
  have functionEqual : (fun step => mul (inverse (add one one))
      (logIntegral (mul (mul (selection.ofRat 2) pi) (variance step)))) =
      (fun step => div (logIntegral (mul (mul (selection.ofRat 2) pi) (variance step)))
        (add one one)) := by
    funext step
    rw [div_eq_mul_inverse, mul_comm]
  rw [functionEqual] at halved
  have derivativeEqual :
      mul (inverse (add one one))
        (mul (inverse (mul (mul (selection.ofRat 2) pi) (variance point)))
          (mul (mul (selection.ofRat 2) pi) varianceRate)) =
      div varianceRate (mul (selection.ofRat 2) (variance point)) := by
    rw [one_add_one, div_eq_mul_inverse, inverse_mul_total (mul (selection.ofRat 2) pi),
      inverse_mul_total (selection.ofRat 2) (variance point)]
    calc mul (inverse (selection.ofRat 2))
          (mul (mul (inverse (mul (selection.ofRat 2) pi)) (inverse (variance point)))
            (mul (mul (selection.ofRat 2) pi) varianceRate))
        = mul (mul varianceRate (mul (inverse (selection.ofRat 2)) (inverse (variance point))))
            (mul (inverse (mul (selection.ofRat 2) pi)) (mul (selection.ofRat 2) pi)) := by
          ac_rfl
      _ = _ := by rw [inverse_mul_cancel (nonzero_of_positive constantPositive), mul_one]
  rwa [derivativeEqual] at halved

/-- The log density differentiates along curves of the mean, the variance, and
the value, at a point of positive variance. -/
public theorem hasDerivative_logDensity_curve
    {mean variance value : selection.Carrier → selection.Carrier}
    {point meanRate varianceRate valueRate : selection.Carrier}
    (meanDifferentiable : HasDerivative mean point meanRate)
    (varianceDifferentiable : HasDerivative variance point varianceRate)
    (valueDifferentiable : HasDerivative value point valueRate)
    (positive : lt zero (variance point)) :
    HasDerivative (fun step => logDensity (mean step) (variance step) (value step)) point
      (logDensitySlope (sub (value point) (mean point)) (variance point)
        (sub valueRate meanRate) varianceRate) := by
  have centered := hasDerivative_sub valueDifferentiable meanDifferentiable
  have quadratic := hasDerivative_quadratic centered varianceDifferentiable
    (nonzero_of_positive positive)
  have combined := hasDerivative_sub (hasDerivative_neg quadratic)
    (hasDerivative_half_log varianceDifferentiable positive)
  have slopeEqual : sub (neg (sub (div (mul (sub (value point) (mean point))
          (sub valueRate meanRate)) (variance point))
        (div (mul (mul (sub (value point) (mean point)) (sub (value point) (mean point)))
          varianceRate) (mul (selection.ofRat 2) (mul (variance point) (variance point))))))
      (div varianceRate (mul (selection.ofRat 2) (variance point))) =
      logDensitySlope (sub (value point) (mean point)) (variance point)
        (sub valueRate meanRate) varianceRate := by
    unfold logDensitySlope
    rw [neg_sub, sub_sub_add]
  rw [slopeEqual] at combined
  exact combined

/-- A differentiable curve that is positive at a point stays positive near it. -/
private theorem positive_near {curve : selection.Carrier → selection.Carrier}
    {point rate : selection.Carrier} (differentiable : HasDerivative curve point rate)
    (positive : lt zero (curve point)) :
    IsNeighborhood (fun value => lt zero (curve value)) point := by
  rcases hasDerivative_continuous differentiable (curve point) positive with
    ⟨radius, radiusPositive, close⟩
  refine ⟨radius, radiusPositive, fun displacement small => ?_⟩
  show lt zero (curve (add point displacement))
  classical
  by_cases same : displacement = zero
  · rw [same, add_zero]
    exact positive
  · have near : lt (abs (sub (curve (add point displacement)) (curve point))) (curve point) :=
      close displacement same small
    have lower := (abs_lt.mp near).left
    have shifted := add_lt_add_right (curve point) lower
    rw [sub_add_cancel, add_comm, add_neg] at shifted
    exact shifted

/-- The density differentiates along curves of the mean, the variance, and the
value, at a point of positive variance, with slope the density times the log
density's slope. -/
public theorem hasDerivative_density_curve
    {mean variance value : selection.Carrier → selection.Carrier}
    {point meanRate varianceRate valueRate : selection.Carrier}
    (meanDifferentiable : HasDerivative mean point meanRate)
    (varianceDifferentiable : HasDerivative variance point varianceRate)
    (valueDifferentiable : HasDerivative value point valueRate)
    (positive : lt zero (variance point)) :
    HasDerivative (fun step => (density (mean step) (variance step) (value step)).toReal) point
      (mul (density (mean point) (variance point) (value point)).toReal
        (logDensitySlope (sub (value point) (mean point)) (variance point)
          (sub valueRate meanRate) varianceRate)) := by
  have exponential := hasDerivative_comp (hasDerivative_exp _)
    (hasDerivative_logDensity_curve meanDifferentiable varianceDifferentiable
      valueDifferentiable positive)
  rw [← density_exp _ _ _ positive] at exponential
  exact HasDerivative.congr_near
    ((positive_near varianceDifferentiable positive).mono fun _ near =>
      (density_exp _ _ _ near).symm) exponential

/-! ### Coordinate cases -/

/-- A line has its rate as derivative everywhere. -/
public theorem hasDerivative_line (base rate point : selection.Carrier) :
    HasDerivative (line base rate) point rate := by
  have moved := hasDerivative_add (hasDerivative_const base point)
    (hasDerivative_smul rate (hasDerivative_identity point))
  rw [mul_one, add_comm zero, add_zero] at moved
  exact moved

/-- The density differentiates in its variance, with slope the density times
`((value - mean)^2 - variance) / (2 variance^2)`. -/
public theorem hasDerivative_density_variance (mean variance value : selection.Carrier)
    (positive : lt zero variance) :
    HasDerivative (fun spread => (density mean spread value).toReal) variance
      (mul (density mean variance value).toReal
        (div (sub (mul (sub value mean) (sub value mean)) variance)
          (mul (selection.ofRat 2) (mul variance variance)))) := by
  have curve := hasDerivative_density_curve (hasDerivative_const mean variance)
    (hasDerivative_identity variance) (hasDerivative_const value variance) positive
  have varianceNonzero := nonzero_of_positive positive
  have slopeEqual : logDensitySlope (sub value mean) variance (sub zero zero) one =
      div (sub (mul (sub value mean) (sub value mean)) variance)
        (mul (selection.ofRat 2) (mul variance variance)) := by
    unfold logDensitySlope
    have unit : div one (mul (selection.ofRat 2) variance) =
        div variance (mul (selection.ofRat 2) (mul variance variance)) := by
      rw [div_eq_mul_inverse, div_eq_mul_inverse, inverse_mul_total, inverse_mul_total,
        inverse_mul_total variance variance]
      calc mul one (mul (inverse (selection.ofRat 2)) (inverse variance))
          = mul (mul (inverse (selection.ofRat 2)) (inverse variance)) one := mul_comm _ _
        _ = mul (mul (inverse (selection.ofRat 2)) (inverse variance))
              (mul variance (inverse variance)) := by rw [mul_inverse_cancel varianceNonzero]
        _ = _ := by ac_rfl
    rw [sub_self, mul_zero, zero_div, add_comm zero, add_zero, mul_one, unit, ← sub_div]
  rw [slopeEqual] at curve
  exact curve

end

end Problib.Analysis.Gaussian
