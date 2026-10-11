module

public import Problib.Analysis.Exponential
public import Problib.Analysis.Real.GeometricSeries

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Logarithm

noncomputable section

/-- Real powers. A positive base gives `exp (exponent * log base)`. A
nonpositive base gives one at exponent zero and zero at every other exponent,
which extends the convention `0 ^ 0 = 1` to the whole nonpositive ray. -/
@[expose] public def rpow (base exponent : Carrier) : Carrier := by
  classical
  exact if lt zero base then exp (mul exponent (logIntegral base))
    else if exponent = zero then one else zero

public theorem rpow_of_positive {base : Carrier} (positive : lt zero base)
    (exponent : Carrier) : rpow base exponent = exp (mul exponent (logIntegral base)) := by
  unfold rpow
  rw [ite_eq_left positive]

public theorem rpow_of_nonpositive {base exponent : Carrier} (nonpositive : le base zero)
    (nonzero : exponent ≠ zero) : rpow base exponent = zero := by
  unfold rpow
  rw [ite_eq_right (fun positive : lt zero base => positive.2 nonpositive), ite_eq_right nonzero]

public theorem zero_rpow {exponent : Carrier} (nonzero : exponent ≠ zero) :
    rpow zero exponent = zero :=
  rpow_of_nonpositive (le_refl zero) nonzero

public theorem rpow_zero (base : Carrier) : rpow base zero = one := by
  classical
  by_cases positive : lt zero base
  · rw [rpow_of_positive positive, zero_mul, exp_zero]
  · unfold rpow
    rw [ite_eq_right positive, ite_eq_left rfl]

public theorem rpow_exp (value exponent : Carrier) :
    rpow (exp value) exponent = exp (mul exponent value) := by
  rw [rpow_of_positive (exp_positive value), log_exp]

public theorem one_rpow (exponent : Carrier) : rpow one exponent = one := by
  rw [rpow_of_positive one_positive, log_one, mul_zero, exp_zero]

private theorem zero_or_positive {base : Carrier} (nonnegative : le zero base) :
    base = zero ∨ lt zero base := by
  classical
  by_cases positive : lt zero base
  · exact Or.inr positive
  · exact Or.inl (le_antisymm (not_lt_iff_le.mp positive) nonnegative)

public theorem rpow_one {base : Carrier} (nonnegative : le zero base) : rpow base one = base := by
  rcases zero_or_positive nonnegative with rfl | positive
  · exact zero_rpow one_ne_zero
  · rw [rpow_of_positive positive, one_mul, exp_log base positive]

public theorem rpow_positive {base : Carrier} (positive : lt zero base) (exponent : Carrier) :
    lt zero (rpow base exponent) := by
  rw [rpow_of_positive positive]
  exact exp_positive _

public theorem rpow_nonnegative (base exponent : Carrier) : le zero (rpow base exponent) := by
  classical
  by_cases positive : lt zero base
  · exact (rpow_positive positive exponent).1
  · by_cases vanishing : exponent = zero
    · rw [vanishing, rpow_zero]
      exact one_nonnegative
    · rw [rpow_of_nonpositive (not_lt_iff_le.mp positive) vanishing]
      exact le_refl zero

/-- Exponents add to a product of powers at every positive base. -/
public theorem rpow_add {base : Carrier} (positive : lt zero base) (first second : Carrier) :
    rpow base (add first second) = mul (rpow base first) (rpow base second) := by
  rw [rpow_of_positive positive, rpow_of_positive positive, rpow_of_positive positive,
    add_mul, exp_add]

/-- A zero base keeps the sum law when the summed exponent is nonzero. -/
public theorem rpow_add_of_nonnegative {base : Carrier} (nonnegative : le zero base)
    {first second : Carrier} (sumNonzero : add first second ≠ zero) :
    rpow base (add first second) = mul (rpow base first) (rpow base second) := by
  classical
  rcases zero_or_positive nonnegative with rfl | positive
  · rw [zero_rpow sumNonzero]
    by_cases firstZero : first = zero
    · have secondNonzero : second ≠ zero := by
        intro secondZero
        apply sumNonzero
        rw [firstZero, secondZero, add_zero]
      rw [zero_rpow secondNonzero, mul_zero]
    · rw [zero_rpow firstZero, zero_mul]
  · exact rpow_add positive first second

public theorem rpow_neg {base : Carrier} (positive : lt zero base) (exponent : Carrier) :
    rpow base (neg exponent) = inverse (rpow base exponent) := by
  rw [rpow_of_positive positive, rpow_of_positive positive, neg_mul, exp_neg]

/-- Powers distribute over a product of nonnegative bases. -/
public theorem mul_rpow {left right : Carrier} (leftNonnegative : le zero left)
    (rightNonnegative : le zero right) (exponent : Carrier) :
    rpow (mul left right) exponent = mul (rpow left exponent) (rpow right exponent) := by
  classical
  by_cases vanishing : exponent = zero
  · rw [vanishing, rpow_zero, rpow_zero, rpow_zero, mul_one]
  rcases zero_or_positive leftNonnegative with rfl | leftPositive
  · rw [zero_mul, zero_rpow vanishing, zero_mul]
  rcases zero_or_positive rightNonnegative with rfl | rightPositive
  · rw [mul_zero, zero_rpow vanishing, mul_zero]
  rw [rpow_of_positive (mul_positive leftPositive rightPositive), rpow_of_positive leftPositive,
    rpow_of_positive rightPositive, log_mul left right leftPositive rightPositive, mul_add,
    exp_add]

/-- Iterated powers multiply their exponents at every nonnegative base. -/
public theorem rpow_mul {base : Carrier} (nonnegative : le zero base) (first second : Carrier) :
    rpow base (mul first second) = rpow (rpow base first) second := by
  classical
  rcases zero_or_positive nonnegative with rfl | positive
  · by_cases firstZero : first = zero
    · rw [firstZero, zero_mul, rpow_zero, one_rpow]
    · rw [zero_rpow firstZero]
      by_cases secondZero : second = zero
      · rw [secondZero, mul_zero, rpow_zero]
      · have productNonzero : mul first second ≠ zero := fun product =>
          (mul_eq_zero_iff.mp product).elim firstZero secondZero
        rw [zero_rpow productNonzero, zero_rpow secondZero]
  · rw [rpow_of_positive positive (mul first second), rpow_of_positive positive first, rpow_exp,
      mul_comm first second, mul_assoc]

/-- A nonnegative base agrees with its natural powers at natural exponents,
including `0 ^ 0 = 1`. -/
public theorem rpow_nat {base : Carrier} (nonnegative : le zero base) (count : Nat) :
    rpow base (selection.ofRat (count : Rat)) =
      Problib.Analysis.Real.SignedSeries.power base count := by
  induction count with
  | zero =>
      rw [show ((0 : Nat) : Rat) = 0 from rfl, ofRat_zero, rpow_zero]
      rfl
  | succ count induction =>
      rcases zero_or_positive nonnegative with rfl | positive
      · have countPositive : lt zero (selection.ofRat ((count + 1 : Nat) : Rat)) :=
          ofRat_succ_positive count
        rw [zero_rpow (nonzero_of_positive countPositive),
          Problib.Analysis.Real.SignedSeries.power_succ, zero_mul]
      · rw [Rat.natCast_add, ofRat_add, show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one,
          rpow_add positive, induction, rpow_one nonnegative,
          Problib.Analysis.Real.SignedSeries.power_succ, mul_comm]

/-- The power is jointly Borel measurable in its base and exponent. -/
public theorem rpow_jointly_measurable :
    MeasurableMap (Space.product borel borel) borel
      (fun pair : Carrier × Carrier => rpow pair.1 pair.2) := by
  classical
  have first : MeasurableMap (Space.product borel borel) borel
      (fun pair : Carrier × Carrier => pair.1) := Space.first_measurable borel borel
  have second : MeasurableMap (Space.product borel borel) borel
      (fun pair : Carrier × Carrier => pair.2) := Space.second_measurable borel borel
  have positive : (Space.product borel borel).Measurable
      (fun pair : Carrier × Carrier => lt zero pair.1) :=
    measurable_lt (MeasurableMap.constant _ borel zero) first
  have vanishing : (Space.product borel borel).Measurable
      (fun pair : Carrier × Carrier => pair.2 = zero) :=
    measurable_eq second (MeasurableMap.constant _ borel zero)
  have inside : MeasurableMap (Space.product borel borel) borel
      (fun pair : Carrier × Carrier => exp (mul pair.2 (logIntegral pair.1))) :=
    MeasurableMap.comp exp_measurable
      (measurable_mul second (MeasurableMap.comp log_measurable first))
  have outside : MeasurableMap (Space.product borel borel) borel
      (fun pair : Carrier × Carrier =>
        @ite Carrier (pair.2 = zero) (Classical.propDecidable _) one zero) :=
    measurable_piecewise vanishing
      (MeasurableMap.constant (Space.product borel borel) borel one)
      (MeasurableMap.constant (Space.product borel borel) borel zero)
  unfold rpow
  intro set measurable
  exact measurable_piecewise positive inside outside measurable

/-- At a fixed exponent the power is Borel measurable in its base. -/
public theorem rpow_measurable (exponent : Carrier) :
    MeasurableMap borel borel (fun base => rpow base exponent) :=
  MeasurableMap.comp rpow_jointly_measurable
    (Space.pair_measurable (MeasurableMap.identity borel)
      (MeasurableMap.constant borel borel exponent))

/-- The sum law needs its guard: at base zero the exponents one and minus one
give `0 ^ 0 = 1` on the left and `0 * 0` on the right. -/
public theorem rpow_add_zero_fails :
    rpow zero (add one (neg one)) ≠ mul (rpow zero one) (rpow zero (neg one)) := by
  rw [add_neg, rpow_zero, zero_rpow one_ne_zero, zero_mul]
  exact one_ne_zero

end
end Problib.Analysis
