module

public import Problib.Analysis.Gaussian.Moment
public import Problib.Analysis.Logarithm.Derivative
public import Problib.Analysis.Real.Dominated
public import Problib.Measure.Integral.Density.Real

/-! An integrable dominator for the Gaussian density's mean secants.

Differentiation under the integral sign in the mean needs one integrable bound
on every secant of the density on a neighborhood of the mean. No mean value
theorem is available, so the bound comes from the exponential's tangent line
`1 + x <= exp x`, which the logarithm's reciprocal rectangles give directly.
The tangent line bounds an increment of the exponential by the exponent's
increment times the sum of the two values. The exponent's increment is linear
in the displacement, and a shifted square is at least half the square less the
radius squared, so every shifted density lies below a fixed multiple of the
Gaussian kernel with doubled variance. The dominator is that kernel weighted by
an affine function of `|value - mean|`, and it is integrable because the Gaussian
law has a finite absolute first moment.
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

/-! ### The exponential's tangent line -/

/-- The exponential lies above its tangent line at zero. -/
public theorem exp_tangent (point : selection.Carrier) : le (add one point) (exp point) := by
  have positive := exp_positive point
  have belowIncrement : le point (sub (exp point) one) := by
    rcases le_total one (exp point) with above | below
    · have bounds := (log_increment_bounds one_positive above).right
      rwa [log_exp, log_one, sub_zero, div_one] at bounds
    · have bounds := (log_increment_bounds positive below).left
      rw [log_exp, log_one, div_one] at bounds
      have flipped := neg_le_neg_iff.mpr bounds
      rwa [neg_sub, neg_sub, sub_zero] at flipped
  have shifted := add_le_add_left_iff (shift := one) |>.mpr belowIncrement
  rwa [add_sub_cancel] at shifted

/-- The tangent line at `left` bounds the exponential's decrease to `right`. -/
private theorem exp_sub_le (left right : selection.Carrier) :
    le (sub (exp left) (exp right)) (mul (exp left) (sub left right)) := by
  have tangent := mul_le_mul_nonnegative_left (exp_tangent (sub right left))
    (le_of_lt (exp_positive left))
  rw [← exp_add, add_sub_cancel] at tangent
  have flipped := neg_le_neg_iff.mpr tangent
  have shifted := add_le_add_left_iff (shift := exp left) |>.mpr flipped
  rw [← sub_eq_add_neg, mul_add, mul_one, neg_add, ← add_assoc, add_neg, add_comm zero, add_zero,
    ← mul_neg, neg_sub] at shifted
  exact shifted

/-- An increment of the exponential is at most the exponent's increment times
the sum of the two values. -/
public theorem abs_exp_sub_le (left right : selection.Carrier) :
    le (abs (sub (exp right) (exp left)))
      (mul (abs (sub right left)) (add (exp left) (exp right))) := by
  have leftNonnegative := le_of_lt (exp_positive left)
  have rightNonnegative := le_of_lt (exp_positive right)
  have rightBelow : le (exp right) (add (exp left) (exp right)) := by
    have shifted := add_le_add_right_iff (shift := exp right) |>.mpr leftNonnegative
    rwa [add_comm zero, add_zero] at shifted
  have leftBelow : le (exp left) (add (exp left) (exp right)) := by
    have shifted := add_le_add_left_iff (shift := exp left) |>.mpr rightNonnegative
    rwa [add_zero] at shifted
  apply abs_le.mpr
  constructor
  · have upper : le (sub (exp left) (exp right))
        (mul (abs (sub right left)) (add (exp left) (exp right))) := by
      refine le_trans (exp_sub_le left right) ?_
      rw [mul_comm (abs _), abs_sub_comm right left]
      exact le_trans (mul_le_mul_nonnegative_left (le_abs (sub left right)) leftNonnegative)
        (mul_le_mul_nonnegative_right leftBelow (abs_nonnegative _))
    have flipped := neg_le_neg_iff.mpr upper
    rwa [neg_sub] at flipped
  · refine le_trans (exp_sub_le right left) ?_
    rw [mul_comm (abs _)]
    exact le_trans (mul_le_mul_nonnegative_left (le_abs (sub right left)) rightNonnegative)
      (mul_le_mul_nonnegative_right rightBelow (abs_nonnegative _))

/-! ### Shifted squares -/

/-- A square is at most twice the square of either part of a split. -/
private theorem square_split_le (first second : selection.Carrier) :
    le (mul (add first second) (add first second))
      (add (add (mul first first) (mul second second))
        (add (mul first first) (mul second second))) := by
  have expand : add (mul (add first second) (add first second))
      (mul (add first (neg second)) (add first (neg second))) =
      add (add (mul first first) (mul second second))
        (add (mul first first) (mul second second)) := by
    simp only [mul_add, add_mul, mul_neg, neg_mul, neg_add, neg_neg]
    calc _ = add (add (add (mul first first) (mul second second))
            (add (mul first first) (mul second second)))
          (add (add (mul second first) (neg (mul second first)))
            (add (mul first second) (neg (mul first second)))) := by ac_rfl
      _ = _ := by rw [add_neg, add_neg, add_zero, add_zero]
  have grown := add_le_add_left_iff (shift := mul (add first second) (add first second))
    |>.mpr (mul_self_nonnegative (add first (neg second)))
  rwa [add_zero, expand] at grown

/-- Twice a value over twice a scale is the value over the scale. -/
private theorem double_div_double (value scale : selection.Carrier) (scaleNonzero : scale ≠ zero) :
    div (add value value) (mul (selection.ofRat 2) scale) = div value scale := by
  rw [add_self, div_eq_mul_inverse, div_eq_mul_inverse, inverse_mul ofRat_two_nonzero scaleNonzero]
  calc mul (mul value two) (mul (inverse (selection.ofRat 2)) (inverse scale))
      = mul (mul value (inverse scale)) (mul (inverse (selection.ofRat 2)) two) := by ac_rfl
    _ = mul value (inverse scale) := by
      rw [show two = selection.ofRat 2 from rfl, inverse_mul_cancel ofRat_two_nonzero, mul_one]

/-- Moving summands across an inequality. -/
private theorem neg_le_add_neg_of_le_add {value first second : selection.Carrier}
    (bounded : le value (add first second)) :
    le (neg first) (add second (neg value)) := by
  have shifted := add_le_add_right_iff (shift := add (neg first) (neg value)) |>.mpr bounded
  have leftSide : add value (add (neg first) (neg value)) = neg first := by
    calc add value (add (neg first) (neg value))
        = add (neg first) (add value (neg value)) := by ac_rfl
      _ = neg first := by rw [add_neg, add_zero]
  have rightSide : add (add first second) (add (neg first) (neg value)) =
      add second (neg value) := by
    calc add (add first second) (add (neg first) (neg value))
        = add (add second (neg value)) (add first (neg first)) := by ac_rfl
      _ = add second (neg value) := by rw [add_neg, add_zero]
  rwa [leftSide, rightSide] at shifted

/-- A square is at most the square of its bound. -/
private theorem square_le_of_abs_le {value bound : selection.Carrier} (small : le (abs value) bound) :
    le (mul value value) (mul bound bound) := by
  have boundNonnegative := le_trans (abs_nonnegative value) small
  have absolute : mul value value = mul (abs value) (abs value) := by
    rw [← abs_mul, abs_of_nonnegative (mul_self_nonnegative value)]
  rw [absolute]
  exact le_trans (mul_le_mul_nonnegative_right small (abs_nonnegative value))
    (mul_le_mul_nonnegative_left small boundNonnegative)

/-- The unnormalized Gaussian kernel `exp (-value^2 / scale)`. -/
@[expose] public def realBell (scale value : selection.Carrier) : selection.Carrier :=
  exp (neg (div (mul value value) scale))

/-- A kernel shifted by at most `radius` lies below the kernel of doubled scale,
grown by `exp (radius^2 / scale)`. -/
public theorem realBell_shift_le {scale radius : selection.Carrier} (positive : lt zero scale)
    (center step : selection.Carrier) (small : le (abs step) radius) :
    le (realBell scale (sub center step))
      (mul (exp (div (mul radius radius) scale))
        (realBell (mul (selection.ofRat 2) scale) center)) := by
  have scaleNonzero := nonzero_of_positive positive
  have doubledPositive := mul_positive ofRat_two_positive positive
  have split := square_split_le (sub center step) step
  rw [sub_add_cancel] at split
  have widened := add_le_add (add_le_add (le_refl (mul (sub center step) (sub center step)))
    (square_le_of_abs_le small)) (add_le_add (le_refl (mul (sub center step) (sub center step)))
    (square_le_of_abs_le small))
  have scaled := div_le_div_right doubledPositive (le_trans split widened)
  rw [double_div_double _ _ scaleNonzero, add_div] at scaled
  have exponent := neg_le_add_neg_of_le_add scaled
  have grown := exp_monotone exponent
  rwa [exp_add] at grown

/-! ### The exponent's increment -/

/-- The kernel exponent's increment under a shift is linear in the shift. -/
private theorem exponent_increment (scale center step : selection.Carrier) :
    sub (neg (div (mul (sub center step) (sub center step)) scale))
        (neg (div (mul center center) scale)) =
      div (mul step (add (sub center step) center)) scale := by
  rw [← neg_sub_distrib, neg_sub, ← sub_div]
  congr 1
  have shifted : center = add (sub center step) step := (sub_add_cancel center step).symm
  generalize sub center step = base at shifted ⊢
  subst shifted
  simp only [mul_add, add_mul]
  rw [sub_eq_add_neg]
  calc add (add (add (mul base base) (mul step base)) (add (mul base step) (mul step step)))
        (neg (mul base base))
      = add (add (mul base base) (neg (mul base base)))
          (add (mul step base) (add (mul base step) (mul step step))) := by ac_rfl
    _ = add (mul step base) (add (mul step base) (mul step step)) := by
      rw [add_neg, add_comm zero, add_zero, mul_comm base step]

/-- The exponent's increment is bounded by the shift times an affine function of
the center. -/
private theorem abs_exponent_increment_le {scale radius : selection.Carrier}
    (positive : lt zero scale) (center step : selection.Carrier)
    (small : le (abs step) radius) :
    le (abs (sub (neg (div (mul (sub center step) (sub center step)) scale))
        (neg (div (mul center center) scale))))
      (mul (abs step) (div (add (add (abs center) (abs center)) radius) scale)) := by
  rw [exponent_increment, abs_div, abs_mul, abs_of_nonnegative (le_of_lt positive), ← mul_div_assoc]
  apply div_le_div_right positive
  apply mul_le_mul_nonnegative_left _ (abs_nonnegative step)
  have shiftedBound : le (abs (sub center step)) (add (abs center) radius) := by
    rw [sub_eq_add_neg]
    refine le_trans (abs_add_le center (neg step)) ?_
    rw [abs_neg]
    exact add_le_add (le_refl (abs center)) small
  refine le_trans (abs_add_le (sub center step) center) ?_
  have sum := add_le_add shiftedBound (le_refl (abs center))
  have reordered : add (add (abs center) radius) (abs center) =
      add (add (abs center) (abs center)) radius := by ac_rfl
  rwa [reordered] at sum

/-! ### The dominator -/

/-- The constant factor of the mean-secant dominator. -/
@[expose] public def meanDominatorScale (variance radius : selection.Carrier) :
    selection.Carrier :=
  div (mul (add (exp (div (mul radius radius) (mul (selection.ofRat 2) variance)))
      (exp (div (mul radius radius) (mul (selection.ofRat 2) variance))))
      (normalizer (mul (selection.ofRat 2) variance)).toReal)
    (mul (mul (selection.ofRat 2) variance) (normalizer variance).toReal)

/-- One bound for every mean secant of the Gaussian density on the neighborhood
of radius `radius`: an affine function of `|value - mean|` times the density of
doubled variance. -/
@[expose] public def meanDominator (mean variance radius value : selection.Carrier) :
    selection.Carrier :=
  mul (mul (meanDominatorScale variance radius)
      (add (add (abs (sub value mean)) (abs (sub value mean))) radius))
    (density mean (mul (selection.ofRat 2) variance) value).toReal

/-- The dominator is nonnegative. -/
public theorem meanDominator_nonnegative (mean variance radius value : selection.Carrier)
    (positive : lt zero variance) (radiusNonnegative : le zero radius) :
    le zero (meanDominator mean variance radius value) := by
  have doubledPositive := mul_positive ofRat_two_positive positive
  have growth := le_of_lt (exp_positive (div (mul radius radius)
    (mul (selection.ofRat 2) variance)))
  have scale : le zero (meanDominatorScale variance radius) :=
    div_nonnegative (mul_nonnegative (add_le_add growth growth |> fun sum => by
        rwa [add_zero] at sum) (le_of_lt (normalizer_positive _ doubledPositive)))
      (le_of_lt (mul_positive doubledPositive (normalizer_positive _ positive)))
  have affine : le zero (add (add (abs (sub value mean)) (abs (sub value mean))) radius) := by
    have sum := add_le_add (add_le_add (abs_nonnegative (sub value mean))
      (abs_nonnegative (sub value mean))) radiusNonnegative
    rwa [add_zero, add_zero] at sum
  exact mul_nonnegative (mul_nonnegative scale affine)
    (le_of_lt (density_positive mean _ doubledPositive value))

/-- The dominator bounds every mean secant of the density at displacements
inside the radius. -/
public theorem mean_secant_le_dominator (mean variance radius value displacement : selection.Carrier)
    (positive : lt zero variance) (nonzero : displacement ≠ zero)
    (small : lt (abs displacement) radius) :
    le (abs (secant (fun center => (density center variance value).toReal) mean displacement))
      (meanDominator mean variance radius value) := by
  have scalePositive := mul_positive ofRat_two_positive positive
  have scaleNonzero := nonzero_of_positive scalePositive
  have normalizerPositive' := normalizer_positive variance positive
  have normalizerNonzero := nonzero_of_positive normalizerPositive'
  have wideNonzero := nonzero_of_positive (normalizer_positive _ scalePositive)
  have stepPositive := abs_positive_of_nonzero nonzero
  have stepNonzero := nonzero_of_positive stepPositive
  have within := le_of_lt small
  have shiftedCenter : sub value (add mean displacement) =
      sub (sub value mean) displacement := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, add_assoc]
  let center := sub value mean
  let growth := exp (div (mul radius radius) (mul (selection.ofRat 2) variance))
  let wide := realBell (mul (selection.ofRat 2) (mul (selection.ofRat 2) variance)) center
  have shiftedBell := realBell_shift_le scalePositive center displacement within
  have baseBell := realBell_shift_le scalePositive center zero
    (by rw [abs_zero]; exact le_trans (abs_nonnegative displacement) within)
  rw [sub_zero] at baseBell
  have increment := abs_exp_sub_le (neg (div (mul center center) (mul (selection.ofRat 2) variance)))
    (neg (div (mul (sub center displacement) (sub center displacement))
      (mul (selection.ofRat 2) variance)))
  have exponentBound := abs_exponent_increment_le scalePositive center displacement within
  have valuesBound := add_le_add baseBell shiftedBell
  have product : le (abs (sub
        (realBell (mul (selection.ofRat 2) variance) (sub center displacement))
        (realBell (mul (selection.ofRat 2) variance) center)))
      (mul (abs displacement)
        (mul (div (add (add (abs center) (abs center)) radius) (mul (selection.ofRat 2) variance))
          (add (mul growth wide) (mul growth wide)))) := by
    refine le_trans increment ?_
    rw [← mul_assoc]
    exact le_trans (mul_le_mul_nonnegative_right exponentBound
        (le_of_lt (add_positive (exp_positive _) (exp_positive _))))
      (mul_le_mul_nonnegative_left valuesBound
        (mul_nonnegative (abs_nonnegative _) (div_nonnegative (by
          have sum := add_le_add (add_le_add (abs_nonnegative center) (abs_nonnegative center))
            (le_trans (abs_nonnegative displacement) within)
          rwa [add_zero, add_zero] at sum) (le_of_lt scalePositive))))
  have secantForm : abs (secant (fun center => (density center variance value).toReal) mean
      displacement) =
      div (div (abs (sub (realBell (mul (selection.ofRat 2) variance) (sub center displacement))
        (realBell (mul (selection.ofRat 2) variance) center))) (normalizer variance).toReal)
        (abs displacement) := by
    rw [secant, density_toReal, density_toReal, shiftedCenter, ← sub_div, abs_div, abs_div,
      abs_of_nonnegative (le_of_lt normalizerPositive')]
    rfl
  rw [secantForm]
  refine le_trans (div_le_div_right stepPositive (div_le_div_right normalizerPositive' product)) ?_
  apply le_of_equal
  have wideForm : wide = mul (density mean (mul (selection.ofRat 2) variance) value).toReal
      (normalizer (mul (selection.ofRat 2) variance)).toReal := by
    rw [density_toReal, div_mul_cancel _ wideNonzero]
    rfl
  rw [wideForm, ← add_mul]
  unfold meanDominator meanDominatorScale
  rw [show exp (div (mul radius radius) (mul (selection.ofRat 2) variance)) = growth from rfl,
    show sub value mean = center from rfl]
  simp only [div_eq_mul_inverse]
  rw [inverse_mul scaleNonzero normalizerNonzero]
  calc _ = mul (mul (mul (mul (add growth growth)
          (normalizer (mul (selection.ofRat 2) variance)).toReal)
          (mul (inverse (mul (selection.ofRat 2) variance)) (inverse (normalizer variance).toReal)))
          (add (add (abs center) (abs center)) radius))
        (mul (density mean (mul (selection.ofRat 2) variance) value).toReal
          (mul (abs displacement) (inverse (abs displacement)))) := by ac_rfl
    _ = _ := by rw [mul_inverse_cancel stepNonzero, mul_one]

/-- The dominator has a certified integral against the reference volume. -/
public theorem meanDominator_hasRealIntegral (mean variance radius : selection.Carrier)
    (positive : lt zero variance) :
    ∃ dominatorValue : selection.Carrier,
      HasRealIntegral volume (meanDominator mean variance radius) dominatorValue := by
  have widePositive := mul_positive ofRat_two_positive positive
  let wide := mul (selection.ofRat 2) variance
  have centered : MeasurableMap borel borel (fun x => sub x mean) :=
    measurable_sub (MeasurableMap.identity borel) (MeasurableMap.constant borel borel mean)
  have pointwise : ∀ x : selection.Carrier,
      ENNReal.le (ENNReal.ofReal (abs (sub x mean)))
        (ENNReal.add (ENNReal.ofReal (sub x mean)) (ENNReal.ofReal (neg (sub x mean)))) := by
    intro x
    rcases le_total zero (sub x mean) with nonnegative | nonpositive
    · rw [abs_of_nonnegative nonnegative]
      have grown := ENNReal.add_le_add_left (ENNReal.zero_le (ENNReal.ofReal (neg (sub x mean))))
        (ENNReal.ofReal (sub x mean))
      rwa [ENNReal.add_zero] at grown
    · rw [abs_of_nonpositive nonpositive]
      have grown := ENNReal.add_le_add_right (ENNReal.zero_le (ENNReal.ofReal (sub x mean)))
        (ENNReal.ofReal (neg (sub x mean)))
      rwa [ENNReal.zero_add] at grown
  have finite := ENNReal.finite_of_le (lintegral_mono (law mean wide) pointwise)
    (absolute_centered_moment_finite mean wide widePositive)
  obtain ⟨mass, massEqual⟩ := ENNReal.exists_finite_of_finite finite
  have absolute : HasRealIntegral (law mean wide) (fun x => abs (sub x mean))
      (sub mass.toReal NNReal.zero.toReal) :=
    ⟨{ positive := fun x => NNReal.ofReal (abs (sub x mean))
       negative := fun _ => NNReal.zero
       positive_measurable := abs_measurable centered
       negative_measurable := ENNRealMeasurable.constant _ _
       decomposition := fun x => by
         rw [NNReal.toReal_ofReal (abs_nonnegative _)]
         exact (sub_zero _).symm
       positiveMass := mass
       negativeMass := NNReal.zero
       positive_integral := massEqual
       negative_integral := lintegral_zero _ }, rfl⟩
  have constant : HasRealIntegral (law mean wide) (fun _ => radius) radius :=
    ⟨IntegralParts.const (law_isProbability mean wide widePositive) radius,
      IntegralParts.const_value _ _⟩
  have scaled := ((absolute.add absolute).add constant).smul (meanDominatorScale variance radius)
  have moved := HasRealIntegral.of_withDensity (measure := volume)
    (density := fun x => density mean wide x) (density_measurable_slice mean wide) scaled
  exact ⟨_, moved⟩

end

end Problib.Analysis.Gaussian
