module

public import Problib.Analysis.Gaussian.Density
public import Problib.Analysis.Exponential.Derivative

/-! The derivative of the Gaussian density.

The density is the exponential of a negated scaled square, divided by a
constant normalizer. The chain rule through `hasDerivative_exp`, with the
product, scaling, and negation rules on the square, differentiates it in any
argument that enters through a differentiable inner function. In the mean the
slope is `density * (value - mean) / variance`, and in the value it is the
negation. Positive variance is used only to cancel the factor two.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩
private instance : Std.Commutative (α := selection.Carrier) mul := ⟨mul_comm⟩

/-- A product with a doubled factor over twice the variance loses the two. -/
private theorem halve_twice (factor variance : selection.Carrier)
    (varianceNonzero : variance ≠ zero) :
    mul (inverse (mul (selection.ofRat 2) variance)) (mul factor (selection.ofRat 2)) =
      mul factor (inverse variance) := by
  rw [inverse_mul ofRat_two_nonzero varianceNonzero]
  calc mul (mul (inverse (selection.ofRat 2)) (inverse variance))
        (mul factor (selection.ofRat 2))
      = mul (mul factor (inverse variance))
          (mul (inverse (selection.ofRat 2)) (selection.ofRat 2)) := by ac_rfl
    _ = mul factor (inverse variance) := by
      rw [inverse_mul_cancel ofRat_two_nonzero, mul_one]

/-- The Gaussian kernel of a differentiable inner function differentiates by
the chain rule. -/
private theorem hasDerivative_kernel {inner : selection.Carrier → selection.Carrier}
    {point innerDerivative : selection.Carrier} (variance : selection.Carrier)
    (varianceNonzero : variance ≠ zero)
    (differentiable : HasDerivative inner point innerDerivative) :
    HasDerivative (fun parameter => div (exp (neg (div
        (mul (inner parameter) (inner parameter))
        (mul (selection.ofRat 2) variance)))) (normalizer variance).toReal) point
      (neg (mul (div (exp (neg (div (mul (inner point) (inner point))
          (mul (selection.ofRat 2) variance)))) (normalizer variance).toReal)
        (div (mul (inner point) innerDerivative) variance))) := by
  have square := hasDerivative_mul differentiable differentiable
  have scaled := hasDerivative_smul (inverse (mul (selection.ofRat 2) variance)) square
  have exponential := hasDerivative_comp (hasDerivative_exp _) (hasDerivative_neg scaled)
  have normalized := hasDerivative_smul (inverse (normalizer variance).toReal) exponential
  have functionEqual : (fun parameter => mul (inverse (normalizer variance).toReal)
      (exp (neg (mul (inverse (mul (selection.ofRat 2) variance))
        (mul (inner parameter) (inner parameter)))))) =
      (fun parameter => div (exp (neg (div (mul (inner parameter) (inner parameter))
        (mul (selection.ofRat 2) variance)))) (normalizer variance).toReal) := by
    funext parameter
    rw [div_eq_mul_inverse, div_eq_mul_inverse, mul_comm (inverse (normalizer variance).toReal),
      mul_comm (inverse (mul (selection.ofRat 2) variance))]
  have doubled : add (mul innerDerivative (inner point)) (mul (inner point) innerDerivative) =
      mul (mul (inner point) innerDerivative) (selection.ofRat 2) := by
    rw [mul_comm innerDerivative (inner point), add_self]
    rfl
  rw [functionEqual, doubled, halve_twice _ variance varianceNonzero] at normalized
  have derivativeEqual :
      mul (inverse (normalizer variance).toReal)
        (mul (exp (neg (mul (inverse (mul (selection.ofRat 2) variance))
            (mul (inner point) (inner point)))))
          (neg (mul (mul (inner point) innerDerivative) (inverse variance)))) =
      neg (mul (div (exp (neg (div (mul (inner point) (inner point))
          (mul (selection.ofRat 2) variance)))) (normalizer variance).toReal)
        (div (mul (inner point) innerDerivative) variance)) := by
    rw [mul_neg, mul_neg, div_eq_mul_inverse, div_eq_mul_inverse, div_eq_mul_inverse,
      mul_comm (mul (inner point) (inner point))]
    congr 1
    ac_rfl
  rwa [derivativeEqual] at normalized

/-- The Gaussian density differentiates in its mean, with slope the density
times the standardized displacement `(value - mean) / variance`. -/
public theorem hasDerivative_density_mean (mean variance value : selection.Carrier)
    (positive : lt zero variance) :
    HasDerivative (fun center => (density center variance value).toReal) mean
      (mul (density mean variance value).toReal (div (sub value mean) variance)) := by
  have varianceNonzero : variance ≠ zero :=
    (positive_iff_nonnegative_and_nonzero.mp positive).2
  have inner := hasDerivative_sub (hasDerivative_const value mean) (hasDerivative_identity mean)
  have kernel := hasDerivative_kernel variance varianceNonzero inner
  have functionEqual : (fun center => (density center variance value).toReal) =
      (fun center => div (exp (neg (div (mul (sub value center) (sub value center))
        (mul (selection.ofRat 2) variance)))) (normalizer variance).toReal) :=
    funext fun center => density_toReal center variance value
  rw [functionEqual, density_toReal]
  have slope : sub zero one = neg one := by
    rw [sub_eq_add_neg, add_comm, add_zero]
  rw [slope, mul_neg, mul_one, neg_div, mul_neg, neg_neg] at kernel
  exact kernel

/-- The Gaussian density differentiates in its value, with slope the negated
mean slope. -/
public theorem hasDerivative_density_value (mean variance value : selection.Carrier)
    (positive : lt zero variance) :
    HasDerivative (fun point => (density mean variance point).toReal) value
      (neg (mul (density mean variance value).toReal (div (sub value mean) variance))) := by
  have varianceNonzero : variance ≠ zero :=
    (positive_iff_nonnegative_and_nonzero.mp positive).2
  have inner := hasDerivative_sub (hasDerivative_identity value) (hasDerivative_const mean value)
  have kernel := hasDerivative_kernel variance varianceNonzero inner
  have functionEqual : (fun point => (density mean variance point).toReal) =
      (fun point => div (exp (neg (div (mul (sub point mean) (sub point mean))
        (mul (selection.ofRat 2) variance)))) (normalizer variance).toReal) :=
    funext fun point => density_toReal mean variance point
  rw [functionEqual, density_toReal]
  rw [sub_zero, mul_one] at kernel
  exact kernel

end

end Problib.Analysis.Gaussian
