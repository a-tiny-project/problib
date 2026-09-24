module

public import Problib.Analysis.Gaussian.LineDominator
public import Problib.Analysis.Gaussian.MeanFamily
public import Problib.Analysis.Real.Leibniz

/-! Bounded tests weighted by the Gaussian density along a line in its mean and
variance.

The line moves the mean at one rate and the variance at another, indexed by the
step from a base point. At every step a bounded measurable test weighted by the
density has a certified integral: where the variance is positive the test is
integrable against the Gaussian law, and where it is not the totalized density
vanishes, so the integral is zero. At a base point of positive variance the
window of steps on which the variance stays between half and twice its base
value is a neighborhood of zero, so the line dominator dominates every secant
there, and the Leibniz rule differentiates the family at step zero with the
test times the density's slope along the line as the pointwise derivative.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩
private instance : Std.Commutative (α := selection.Carrier) mul := ⟨mul_comm⟩

private theorem doubled (value : selection.Carrier) :
    add value value = mul (selection.ofRat 2) value := by
  rw [← one_add_one, add_mul, one_mul]

private theorem halves_add (value : selection.Carrier) :
    add (div value (selection.ofRat 2)) (div value (selection.ofRat 2)) = value := by
  rw [doubled, div_eq_mul_inverse, mul_comm value, ← mul_assoc, mul_inverse_cancel ofRat_two_nonzero,
    one_mul]

/-! ### The density outside its probability domain -/

/-- At a nonpositive variance the totalized density vanishes: the normalizer is
zero, and division by zero is zero. -/
public theorem density_nonpositive (mean variance value : selection.Carrier)
    (nonpositive : le variance zero) : density mean variance value = NNReal.zero := by
  have constant : le zero (mul (selection.ofRat 2) pi) :=
    le_of_lt (mul_positive ofRat_two_positive pi_positive)
  have product : le (mul (mul (selection.ofRat 2) pi) variance) zero := by
    have scaled := mul_le_mul_nonnegative_left nonpositive constant
    rwa [mul_zero] at scaled
  unfold density normalizer
  rw [NNReal.ofReal_eq_zero_iff.mpr product, sqrt_zero, NNReal.toReal_zero, div_eq_mul_inverse,
    inverse_zero, mul_zero]
  exact NNReal.ofReal_eq_zero_iff.mpr (le_refl zero)

/-! ### The window -/

/-- The step radius on which the variance stays between half and twice its
base value. -/
@[expose] public def lineRadius (variance varianceRate : selection.Carrier) : selection.Carrier :=
  div variance (mul (selection.ofRat 2) (add (abs varianceRate) one))

/-- At a positive base variance the window is a neighborhood of step zero. -/
public theorem lineRadius_window {variance : selection.Carrier} (positive : lt zero variance)
    (meanRate varianceRate : selection.Carrier) :
    lt zero (lineRadius variance varianceRate) ∧
      ∀ step, lt (abs step) (lineRadius variance varianceRate) →
        InLineWindow variance meanRate varianceRate (div variance (selection.ofRat 2))
          (mul (selection.ofRat 2) variance)
          (mul (abs meanRate) (lineRadius variance varianceRate)) step := by
  have ratePositive : lt zero (add (abs varianceRate) one) := by
    have grown := add_le_add (abs_nonnegative varianceRate) (le_refl one)
    rw [add_comm zero one, add_zero] at grown
    exact lt_of_lt_of_le one_positive grown
  have radiusPositive : lt zero (lineRadius variance varianceRate) :=
    mul_positive positive (inverse_of_positive_positive (mul_positive ofRat_two_positive ratePositive))
  have halfNonnegative : le zero (div variance (selection.ofRat 2)) :=
    le_of_lt (mul_positive positive (inverse_of_positive_positive ofRat_two_positive))
  refine ⟨radiusPositive, fun step small => ?_⟩
  have stepBelow := le_of_lt small
  have radiusNonnegative := le_of_lt radiusPositive
  -- The variance moves by at most half its base value.
  have moveBound : le (abs (mul varianceRate step)) (div variance (selection.ofRat 2)) := by
    rw [abs_mul]
    refine le_trans (mul_le_mul_nonnegative_left stepBelow (abs_nonnegative varianceRate)) ?_
    have grown := add_le_add (le_refl (mul (abs varianceRate) (lineRadius variance varianceRate)))
      radiusNonnegative
    rw [add_zero] at grown
    refine le_trans grown (le_of_equal ?_)
    rw [show add (mul (abs varianceRate) (lineRadius variance varianceRate))
        (lineRadius variance varianceRate) =
        mul (add (abs varianceRate) one) (lineRadius variance varianceRate) by
      rw [add_mul, one_mul]]
    unfold lineRadius
    rw [div_eq_mul_inverse, div_eq_mul_inverse,
      inverse_mul ofRat_two_nonzero (nonzero_of_positive ratePositive)]
    calc _ = mul (mul variance (inverse (selection.ofRat 2)))
          (mul (add (abs varianceRate) one) (inverse (add (abs varianceRate) one))) := by ac_rfl
      _ = _ := by rw [mul_inverse_cancel (nonzero_of_positive ratePositive), mul_one]
  obtain ⟨lowerSide, upperSide⟩ := abs_le.mp moveBound
  refine ⟨?_, ?_, ?_⟩
  · show le (div variance (selection.ofRat 2)) (add variance (mul varianceRate step))
    have shifted := add_le_add (le_refl variance) lowerSide
    refine le_trans (le_of_equal ?_) shifted
    have restored : add variance (neg (div variance (selection.ofRat 2))) =
        add (add (div variance (selection.ofRat 2)) (div variance (selection.ofRat 2)))
          (neg (div variance (selection.ofRat 2))) := by
      rw [halves_add]
    rw [restored, add_assoc, add_neg, add_zero]
  · show le (add variance (mul varianceRate step)) (mul (selection.ofRat 2) variance)
    have half : le (div variance (selection.ofRat 2)) variance := by
      have grown := add_le_add (le_refl (div variance (selection.ofRat 2))) halfNonnegative
      rw [add_zero, halves_add] at grown
      exact grown
    rw [← doubled]
    exact add_le_add (le_refl variance) (le_trans upperSide half)
  · rw [abs_mul]
    exact mul_le_mul_nonnegative_left stepBelow (abs_nonnegative meanRate)

/-! ### The family -/

/-- A bounded measurable test weighted by the density at every step of the
line has a certified integral, zero where the variance is not positive. -/
public theorem line_test_hasRealIntegral {mean variance meanRate varianceRate bound :
    selection.Carrier} {test : selection.Carrier → selection.Carrier}
    (measurable : MeasurableMap borel borel test)
    (bounded : ∀ value, le (abs (test value)) bound) (step : selection.Carrier) :
    ∃ integral : selection.Carrier,
      HasRealIntegral volume (fun value => mul (test value)
        (density (line mean meanRate step) (line variance varianceRate step) value).toReal)
        integral := by
  classical
  by_cases positive : lt zero (line variance varianceRate step)
  · exact bounded_test_hasRealIntegral positive measurable bounded
  · have nonpositive : le (line variance varianceRate step) zero := not_lt_iff_le.mp positive
    obtain ⟨integral, certified⟩ := bounded_test_hasRealIntegral (mean := zero) one_positive
      measurable bounded
    have vanished : HasRealIntegral volume
        (fun value => mul zero (mul (test value) (density zero one value).toReal)) zero := by
      have scaled := certified.smul zero
      rwa [zero_mul integral] at scaled
    refine ⟨zero, vanished.congr (fun value => ?_)⟩
    rw [zero_mul, density_nonpositive _ _ _ nonpositive, NNReal.toReal_zero, mul_zero]

/-- A bounded measurable test weighted by the density along the line, as a
certified integral family in the step. -/
@[expose] public def lineFamily (mean variance meanRate varianceRate bound : selection.Carrier)
    (test : selection.Carrier → selection.Carrier) (measurable : MeasurableMap borel borel test)
    (bounded : ∀ value, le (abs (test value)) bound) : IntegralFamily volume where
  integrand := fun step value => mul (test value)
    (density (line mean meanRate step) (line variance varianceRate step) value).toReal
  value := fun step => Classical.choose (line_test_hasRealIntegral (mean := mean)
    (variance := variance) (meanRate := meanRate) (varianceRate := varianceRate)
    measurable bounded step)
  certified := fun step => Classical.choose_spec (line_test_hasRealIntegral (mean := mean)
    (variance := variance) (meanRate := meanRate) (varianceRate := varianceRate)
    measurable bounded step)

/-- The test times the density's slope along the line, the pointwise
derivative of the line family at step zero. -/
@[expose] public def lineScore (mean variance meanRate varianceRate : selection.Carrier)
    (test : selection.Carrier → selection.Carrier) (value : selection.Carrier) :
    selection.Carrier :=
  mul (test value) (mul (density mean variance value).toReal
    (logDensitySlope (sub value mean) variance (neg meanRate) varianceRate))

/-- The bound times the line dominator dominates every secant of the line
family at step zero on the window. -/
public theorem lineFamily_dominated {mean variance meanRate varianceRate bound :
    selection.Carrier} (positive : lt zero variance)
    {test : selection.Carrier → selection.Carrier} (measurable : MeasurableMap borel borel test)
    (bounded : ∀ value, le (abs (test value)) bound) :
    HasDominatedDifferenceQuotients
      (lineFamily mean variance meanRate varianceRate bound test measurable bounded) zero := by
  obtain ⟨radiusPositive, window⟩ := lineRadius_window positive meanRate varianceRate
  have boundNonnegative : le zero bound := le_trans (abs_nonnegative (test zero)) (bounded zero)
  have lowerPositive : lt zero (div variance (selection.ofRat 2)) :=
    mul_positive positive (inverse_of_positive_positive ofRat_two_positive)
  have reachNonnegative : le zero (mul (abs meanRate) (lineRadius variance varianceRate)) :=
    mul_nonnegative (abs_nonnegative _) (le_of_lt radiusPositive)
  obtain ⟨dominatorValue, dominatorIntegral⟩ := lineDominator_hasRealIntegral mean meanRate
    varianceRate (div variance (selection.ofRat 2)) (mul (selection.ofRat 2) variance)
    (mul (abs meanRate) (lineRadius variance varianceRate)) (mul_positive ofRat_two_positive positive)
  refine ⟨lineRadius variance varianceRate, fun value => mul bound (lineDominator mean meanRate
    varianceRate (div variance (selection.ofRat 2)) (mul (selection.ofRat 2) variance)
    (mul (abs meanRate) (lineRadius variance varianceRate)) value),
    mul bound dominatorValue, radiusPositive, dominatorIntegral.smul bound,
    fun value => mul_nonnegative boundNonnegative
      (lineDominator_nonnegative _ _ _ _ _ _ value lowerPositive reachNonnegative),
    fun displacement nonzero small value => ?_⟩
  have factored : secant (fun step => mul (test value)
      (density (line mean meanRate step) (line variance varianceRate step) value).toReal)
      zero displacement =
      mul (test value) (secant (fun step =>
        (density (line mean meanRate step) (line variance varianceRate step) value).toReal)
        zero displacement) := by
    rw [secant, secant, ← mul_sub, mul_div_assoc]
  show le (abs (secant (fun step => mul (test value)
    (density (line mean meanRate step) (line variance varianceRate step) value).toReal)
    zero displacement)) _
  rw [factored, abs_mul]
  exact le_trans (mul_le_mul_nonnegative_right (bounded value) (abs_nonnegative _))
    (mul_le_mul_nonnegative_left
      (line_secant_le_dominator lowerPositive radiusPositive window value displacement nonzero small)
      boundNonnegative)

/-- The line family differentiates under the integral sign at step zero, with
the test times the density's slope along the line as the pointwise
derivative. -/
public theorem lineFamily_differentiatesUnderIntegral {mean variance meanRate varianceRate bound :
    selection.Carrier} (positive : lt zero variance)
    {test : selection.Carrier → selection.Carrier} (measurable : MeasurableMap borel borel test)
    (bounded : ∀ value, le (abs (test value)) bound) :
    ∃ derivative : selection.Carrier,
      DifferentiatesUnderIntegral
        (lineFamily mean variance meanRate varianceRate bound test measurable bounded) zero
        (lineScore mean variance meanRate varianceRate test) derivative := by
  have constant (value : selection.Carrier) :
      MeasurableMap borel borel (fun _ : selection.Carrier => value) :=
    MeasurableMap.constant borel borel value
  have centered : MeasurableMap borel borel (fun value => sub value mean) :=
    measurable_sub (MeasurableMap.identity borel) (constant mean)
  have densityMeasurable : MeasurableMap borel borel
      (fun value => (density mean variance value).toReal) := by
    have formula : MeasurableMap borel borel (fun value => div (exp (neg (div
        (mul (sub value mean) (sub value mean)) (mul (selection.ofRat 2) variance))))
        (normalizer variance).toReal) :=
      measurable_div (MeasurableMap.comp exp_measurable (MeasurableMap.comp neg_measurable
        (measurable_div (measurable_mul centered centered) (constant _))))
        (constant _)
    have equal : (fun value => (density mean variance value).toReal) =
        (fun value => div (exp (neg (div (mul (sub value mean) (sub value mean))
          (mul (selection.ofRat 2) variance)))) (normalizer variance).toReal) :=
      funext fun value => density_toReal mean variance value
    rw [equal]
    intro set measurableSet
    exact formula measurableSet
  have slopeMeasurable : MeasurableMap borel borel (fun value =>
      logDensitySlope (sub value mean) variance (neg meanRate) varianceRate) :=
    measurable_sub
      (measurable_div (measurable_mul (measurable_mul centered centered) (constant _))
        (constant _))
      (measurable_add (measurable_div (measurable_mul centered (constant _)) (constant _))
        (constant _))
  have scoreMeasurable : MeasurableMap borel borel
      (lineScore mean variance meanRate varianceRate test) :=
    measurable_mul measurable (measurable_mul densityMeasurable slopeMeasurable)
  refine differentiatesUnderIntegral_of_dominated
    (lineFamily_dominated positive measurable bounded) (fun value => ?_) scoreMeasurable
  have curve := hasDerivative_density_curve (hasDerivative_line mean meanRate zero)
    (hasDerivative_line variance varianceRate zero) (hasDerivative_const value zero)
    (by rw [line_at_zero]; exact positive)
  have scaled := hasDerivative_smul (test value) curve
  rw [line_at_zero, line_at_zero, zero_sub] at scaled
  exact scaled

end

end Problib.Analysis.Gaussian
