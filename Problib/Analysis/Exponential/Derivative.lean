module

public import Problib.Analysis.Exponential
public import Problib.Analysis.Logarithm.Derivative

/-! The derivative of the exponential.

The exponential is the order inverse of the integral logarithm, so its
derivative comes from the inverse-function rule once it is continuous.
Continuity at zero is order-theoretic: a displacement inside the logarithms of
`1 - η` and `1 + η` moves the exponential by less than `η`, because both are
strictly monotone and each undoes the other on the positive ray. Continuity
elsewhere is the product law `exp_add`. The logarithm's derivative at `exp y` is
`1 / exp y`, and its reciprocal is `exp y`.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real Logarithm

noncomputable section

/-- The exponential approaches one at zero. -/
public theorem exp_approaches_one : Approaches exp one := by
  intro epsilon positive
  rcases small_positive positive (half_positive one_positive) with
    ⟨tolerance, tolerancePositive, belowEpsilon, belowHalf⟩
  have toleranceBelowOne : lt tolerance one := by
    refine lt_of_le_of_lt belowHalf ?_
    have doubled := add_lt_add_left (half one) (half_positive one_positive)
    rwa [add_half, add_zero] at doubled
  have upperPositive : lt zero (add one tolerance) := by
    have shifted := add_lt_add_left one tolerancePositive
    rw [add_zero] at shifted
    exact lt_trans one_positive shifted
  have lowerPositive : lt zero (sub one tolerance) := sub_positive_iff.mpr toleranceBelowOne
  have upperGap : lt zero (logIntegral (add one tolerance)) := by
    have grown := log_strict one (add one tolerance) one_positive (by
      have shifted := add_lt_add_left one tolerancePositive
      rwa [add_zero] at shifted)
    rwa [log_one] at grown
  have lowerGap : lt zero (neg (logIntegral (sub one tolerance))) := by
    have shrunk := log_strict (sub one tolerance) one lowerPositive (by
      have shifted := add_lt_add_left one (neg_negative_iff.mp tolerancePositive)
      rwa [add_zero, ← sub_eq_add_neg] at shifted)
    rw [log_one] at shrunk
    exact neg_positive_iff.mpr shrunk
  rcases small_positive upperGap lowerGap with
    ⟨radius, radiusPositive, belowUpper, belowLower⟩
  refine ⟨radius, radiusPositive, fun displacement _ inside => ?_⟩
  have bounds := abs_lt.mp inside
  have aboveLower : lt (logIntegral (sub one tolerance)) displacement := by
    have reflected := neg_le_neg_iff.mpr belowLower
    rw [neg_neg] at reflected
    exact lt_of_le_of_lt reflected bounds.left
  have belowUpperValue : lt displacement (logIntegral (add one tolerance)) :=
    lt_of_lt_of_le bounds.right belowUpper
  have expAbove := exp_strict aboveLower
  have expBelow := exp_strict belowUpperValue
  rw [exp_log _ lowerPositive] at expAbove
  rw [exp_log _ upperPositive] at expBelow
  refine lt_of_lt_of_le (abs_lt.mpr ⟨?_, ?_⟩) belowEpsilon
  · have shifted := add_lt_add_right (neg one) expAbove
    rwa [← sub_eq_add_neg, ← sub_eq_add_neg, sub_eq_add_neg one tolerance, add_sub_self] at shifted
  · have shifted := add_lt_add_right (neg one) expBelow
    rwa [← sub_eq_add_neg, ← sub_eq_add_neg, add_sub_self] at shifted

/-- The exponential is continuous at every point. -/
public theorem exp_continuous (point : selection.Carrier) :
    Approaches (fun displacement => exp (add point displacement)) (exp point) := by
  have product := approaches_mul (approaches_const (exp point)) exp_approaches_one
  rw [mul_one] at product
  refine approaches_congr_near one_positive (fun displacement _ _ => ?_) product
  exact (exp_add point displacement).symm

/-- The exponential differentiates to itself. -/
public theorem hasDerivative_exp (point : selection.Carrier) :
    HasDerivative exp point (exp point) := by
  have positive := exp_positive point
  have valueNonzero : inverse (exp point) ≠ zero := by
    apply inverse_nonzero
    intro vanished
    rw [vanished] at positive
    exact lt_irrefl zero positive
  have derivative := hasDerivative_of_right_inverse (forward := logIntegral) (backward := exp)
    one_positive (fun displacement _ => log_exp (add point displacement))
    (exp_continuous point) (hasDerivative_log positive) valueNonzero
  rwa [inverse_inverse] at derivative

end

end Problib.Analysis
