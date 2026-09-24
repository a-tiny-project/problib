module

public import Problib.Analysis.Gaussian.Curve
public import Problib.Analysis.Gaussian.Dominator
public import Problib.Analysis.Gaussian.SecondMoment

/-! A dominator for the Gaussian density's secants along a line in its mean and
variance.

The line moves the mean at rate `meanRate` and the variance at rate
`varianceRate`. On a window of steps where the variance stays in a closed
interval `[lower, upper]` of positive variances and the mean moves by at most
`reach`, one integrable function bounds every secant at step zero. The density
is the exponential of its log density, so the tangent-line bound `abs_exp_sub_le`
reduces an increment of the density to an increment of the log density times
two values of the density. The log density's increment is the step times a
quadratic in `|value - mean|`: a linear term from the moving mean, a quadratic
term from the moving reciprocal variance, and a constant from the moving
logarithm, each with the interval's lower end in its denominator. Every value
of the density on the window lies below a grown kernel of variance twice the
upper end. The dominator is the quadratic times that kernel, integrable through
the absolute and second moments of the Gaussian law with that variance.
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

/-- A product of bounded nonnegative factors is bounded by the product of the
bounds. -/
private theorem mul_le_mul_both {first second firstBound secondBound : selection.Carrier}
    (firstNonnegative : le zero first) (secondNonnegative : le zero second)
    (firstBelow : le first firstBound) (secondBelow : le second secondBound) :
    le (mul first second) (mul firstBound secondBound) :=
  le_trans (mul_le_mul_nonnegative_right firstBelow secondNonnegative)
    (mul_le_mul_nonnegative_left secondBelow (le_trans firstNonnegative firstBelow))

/-- The logarithm's increment between two values above a positive floor is at
most their distance over the floor. -/
private theorem abs_log_sub_le {first second floor : selection.Carrier} (floorPositive : lt zero floor)
    (firstAbove : le floor first) (secondAbove : le floor second) :
    le (abs (sub (logIntegral first) (logIntegral second)))
      (div (abs (sub first second)) floor) := by
  have firstPositive := lt_of_lt_of_le floorPositive firstAbove
  have secondPositive := lt_of_lt_of_le floorPositive secondAbove
  rcases le_total first second with ordered | ordered
  · have bound := (log_increment_bounds firstPositive ordered).right
    have increase := sub_nonnegative (log_monotone first second firstPositive ordered)
    have gap := sub_nonnegative ordered
    rw [abs_sub_comm, abs_of_nonnegative increase, abs_sub_comm, abs_of_nonnegative gap]
    exact le_trans bound (div_le_div_of_positive gap floorPositive firstAbove)
  · have bound := (log_increment_bounds secondPositive ordered).right
    have increase := sub_nonnegative (log_monotone second first secondPositive ordered)
    have gap := sub_nonnegative ordered
    rw [abs_of_nonnegative increase, abs_of_nonnegative gap]
    exact le_trans bound (div_le_div_of_positive gap floorPositive secondAbove)

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

/-- The mean on the line, read from the value, is the centered value less the
mean's move. -/
private theorem shifted_center (mean meanRate value step : selection.Carrier) :
    sub value (line mean meanRate step) = sub (sub value mean) (mul meanRate step) := by
  simp only [line]
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, add_assoc]

/-! ### The increment's parts -/

/-- The log density's increment splits around any middle value into the moving
mean's part, the moving variance's part, and the moving logarithm's part. -/
private theorem increment_split (moved base movedLog baseLog middle : selection.Carrier) :
    sub (sub (neg moved) movedLog) (sub (neg base) baseLog) =
      add (add (sub middle moved) (sub base middle)) (sub baseLog movedLog) := by
  simp only [sub_eq_add_neg, neg_add, neg_neg]
  rw [show add (add (add middle (neg moved)) (add base (neg middle))) (add baseLog (neg movedLog)) =
      add (add middle (neg middle)) (add (add (neg moved) (neg movedLog)) (add base baseLog)) by
    ac_rfl, add_neg, add_comm zero, add_zero]

/-- The moving mean's part is the step times an affine function of the
centered value. -/
private theorem mean_part_le {scale floor reach center shift meanRate step : selection.Carrier}
    (scalePositive : lt zero scale) (floorPositive : lt zero floor) (floorBelow : le floor scale)
    (shiftEqual : shift = mul meanRate step) (moved : le (abs shift) reach) :
    le (abs (sub (div (mul center center) scale)
        (div (mul (sub center shift) (sub center shift)) scale)))
      (mul (abs step) (mul (div (abs meanRate) floor) (add (add (abs center) (abs center)) reach))) := by
  have flipped : sub (div (mul center center) scale)
      (div (mul (sub center shift) (sub center shift)) scale) =
      sub (neg (div (mul (sub center shift) (sub center shift)) scale))
        (neg (div (mul center center) scale)) := by
    rw [← neg_sub_distrib, neg_sub]
  rw [flipped, exponent_increment, abs_div, abs_mul, abs_of_nonnegative (le_of_lt scalePositive)]
  have shiftedBound : le (abs (sub center shift)) (add (abs center) reach) := by
    rw [sub_eq_add_neg]
    refine le_trans (abs_add_le center (neg shift)) ?_
    rw [abs_neg]
    exact add_le_add (le_refl (abs center)) moved
  have sumBound : le (abs (add (sub center shift) center))
      (add (add (abs center) (abs center)) reach) := by
    refine le_trans (abs_add_le _ _) ?_
    have sum := add_le_add shiftedBound (le_refl (abs center))
    have reordered : add (add (abs center) reach) (abs center) =
        add (add (abs center) (abs center)) reach := by ac_rfl
    rwa [reordered] at sum
  have reachNonnegative : le zero reach := le_trans (abs_nonnegative _) moved
  have affineNonnegative : le zero (add (add (abs center) (abs center)) reach) :=
    add_nonnegative (add_nonnegative (abs_nonnegative _) (abs_nonnegative _)) reachNonnegative
  refine le_trans (div_le_div_right scalePositive
    (mul_le_mul_nonnegative_left sumBound (abs_nonnegative shift))) ?_
  refine le_trans (div_le_div_of_positive (mul_nonnegative (abs_nonnegative _) affineNonnegative)
    floorPositive floorBelow) (le_of_equal ?_)
  subst shiftEqual
  rw [abs_mul]
  simp only [div_eq_mul_inverse]
  ac_rfl

/-- The moving reciprocal variance's part is the step times a multiple of the
centered square. -/
private theorem variance_part_le {lower base moving center rate step : selection.Carrier}
    (lowerPositive : lt zero lower) (baseAbove : le lower base) (movingAbove : le lower moving)
    (move : sub moving base = mul rate step) :
    le (abs (sub (div (mul center center) (mul (selection.ofRat 2) base))
        (div (mul center center) (mul (selection.ofRat 2) moving))))
      (mul (abs step)
        (mul (div (abs rate) (mul (selection.ofRat 2) (mul lower lower))) (mul center center))) := by
  have doubledLower := mul_positive ofRat_two_positive lowerPositive
  have baseScale := mul_positive ofRat_two_positive (lt_of_lt_of_le lowerPositive baseAbove)
  have movingScale := mul_positive ofRat_two_positive (lt_of_lt_of_le lowerPositive movingAbove)
  rw [div_eq_mul_inverse, div_eq_mul_inverse, ← mul_sub,
    inverse_sub (nonzero_of_positive baseScale) (nonzero_of_positive movingScale), ← mul_sub, move,
    abs_mul, abs_of_nonnegative (mul_self_nonnegative center), abs_div, abs_mul, abs_mul,
    abs_of_nonnegative (le_of_lt ofRat_two_positive),
    abs_of_nonnegative (le_of_lt (mul_positive baseScale movingScale))]
  have floor : le (mul (mul (selection.ofRat 2) lower) (mul (selection.ofRat 2) lower))
      (mul (mul (selection.ofRat 2) base) (mul (selection.ofRat 2) moving)) :=
    mul_le_mul_both (le_of_lt doubledLower) (le_of_lt doubledLower)
      (mul_le_mul_nonnegative_left baseAbove (le_of_lt ofRat_two_positive))
      (mul_le_mul_nonnegative_left movingAbove (le_of_lt ofRat_two_positive))
  refine le_trans (mul_le_mul_nonnegative_left (div_le_div_of_positive
    (mul_nonnegative (le_of_lt ofRat_two_positive)
      (mul_nonnegative (abs_nonnegative _) (abs_nonnegative _)))
    (mul_positive doubledLower doubledLower) floor) (mul_self_nonnegative center)) (le_of_equal ?_)
  simp only [div_eq_mul_inverse, inverse_mul_total]
  calc _ = mul (mul (abs step) (mul (mul (abs rate)
          (mul (inverse (selection.ofRat 2)) (mul (inverse lower) (inverse lower))))
          (mul center center))) (mul (selection.ofRat 2) (inverse (selection.ofRat 2))) := by
        ac_rfl
    _ = _ := by rw [mul_inverse_cancel ofRat_two_nonzero, mul_one]

/-- The moving logarithm's part is the step times a constant. -/
private theorem log_part_le {lower base moving rate step : selection.Carrier}
    (lowerPositive : lt zero lower) (baseAbove : le lower base) (movingAbove : le lower moving)
    (move : sub moving base = mul rate step) :
    le (abs (sub (div (logIntegral (mul (mul (selection.ofRat 2) pi) base)) (add one one))
        (div (logIntegral (mul (mul (selection.ofRat 2) pi) moving)) (add one one))))
      (mul (abs step) (div (abs rate) (mul (selection.ofRat 2) lower))) := by
  have constantPositive : lt zero (mul (selection.ofRat 2) pi) :=
    mul_positive ofRat_two_positive pi_positive
  have bound := abs_log_sub_le (mul_positive constantPositive lowerPositive)
    (mul_le_mul_nonnegative_left baseAbove (le_of_lt constantPositive))
    (mul_le_mul_nonnegative_left movingAbove (le_of_lt constantPositive))
  rw [← sub_div, abs_div, one_add_one, abs_of_nonnegative (le_of_lt ofRat_two_positive)]
  refine le_trans (div_le_div_right ofRat_two_positive bound) (le_of_equal ?_)
  rw [← mul_sub, ← neg_sub moving base, move, abs_mul (mul (selection.ofRat 2) pi),
    abs_of_nonnegative (le_of_lt constantPositive), abs_neg, abs_mul rate step]
  simp only [div_eq_mul_inverse, inverse_mul_total]
  calc _ = mul (mul (abs step) (mul (abs rate) (mul (inverse (selection.ofRat 2)) (inverse lower))))
        (mul (mul (selection.ofRat 2) (inverse (selection.ofRat 2))) (mul pi (inverse pi))) := by
        ac_rfl
    _ = _ := by
      rw [mul_inverse_cancel ofRat_two_nonzero, mul_inverse_cancel (nonzero_of_positive pi_positive),
        mul_one, mul_one]

/-! ### The dominator -/

/-- The quadratic in the centered value that bounds the log density's
increment per unit step. -/
@[expose] public def lineIncrementBound (meanRate varianceRate lower reach center :
    selection.Carrier) : selection.Carrier :=
  add (add (mul (div (abs meanRate) (mul (selection.ofRat 2) lower))
        (add (add (abs center) (abs center)) reach))
      (mul (div (abs varianceRate) (mul (selection.ofRat 2) (mul lower lower)))
        (mul center center)))
    (div (abs varianceRate) (mul (selection.ofRat 2) lower))

/-- The constant that grows the density of variance twice the upper end past
every density value on the window. -/
@[expose] public def lineGrowth (lower upper reach : selection.Carrier) : selection.Carrier :=
  div (mul (exp (div (mul reach reach) (mul (selection.ofRat 2) upper)))
      (normalizer (mul (selection.ofRat 2) upper)).toReal)
    (normalizer lower).toReal

/-- The bound on every density value on the window: a multiple of the density
of variance twice the upper end. -/
@[expose] public def lineEnvelope (mean lower upper reach value : selection.Carrier) :
    selection.Carrier :=
  mul (lineGrowth lower upper reach) (density mean (mul (selection.ofRat 2) upper) value).toReal

/-- One bound for every secant at step zero of the density along the line. -/
@[expose] public def lineDominator (mean meanRate varianceRate lower upper reach value :
    selection.Carrier) : selection.Carrier :=
  mul (lineIncrementBound meanRate varianceRate lower reach (sub value mean))
    (add (lineEnvelope mean lower upper reach value) (lineEnvelope mean lower upper reach value))

/-- The window: steps where the variance stays in `[lower, upper]` and the mean
moves by at most `reach`. -/
@[expose] public def InLineWindow (variance meanRate varianceRate lower upper reach step :
    selection.Carrier) : Prop :=
  le lower (line variance varianceRate step) ∧ le (line variance varianceRate step) upper ∧
    le (abs (mul meanRate step)) reach

/-- Every density value on the window lies below the envelope. -/
public theorem density_le_lineEnvelope {mean variance meanRate varianceRate lower upper reach
    step : selection.Carrier} (lowerPositive : lt zero lower)
    (window : InLineWindow variance meanRate varianceRate lower upper reach step)
    (value : selection.Carrier) :
    le (density (line mean meanRate step) (line variance varianceRate step) value).toReal
      (lineEnvelope mean lower upper reach value) := by
  obtain ⟨above, below, moved⟩ := window
  have variancePositive := lt_of_lt_of_le lowerPositive above
  have upperPositive := lt_of_lt_of_le variancePositive below
  have scalePositive := mul_positive ofRat_two_positive variancePositive
  have wideScalePositive := mul_positive ofRat_two_positive upperPositive
  have lowerNormalizer := normalizer_positive lower lowerPositive
  have wideNormalizer := normalizer_positive (mul (selection.ofRat 2) upper) wideScalePositive
  have bell : realBell (mul (selection.ofRat 2) (mul (selection.ofRat 2) upper)) (sub value mean) =
      mul (density mean (mul (selection.ofRat 2) upper) value).toReal
        (normalizer (mul (selection.ofRat 2) upper)).toReal := by
    rw [density_toReal, div_eq_mul_inverse, mul_assoc,
      mul_comm (inverse _), mul_inverse_cancel (nonzero_of_positive wideNormalizer), mul_one]
    rfl
  rw [density_toReal, shifted_center]
  have wider : le (exp (neg (div (mul (sub (sub value mean) (mul meanRate step))
        (sub (sub value mean) (mul meanRate step)))
        (mul (selection.ofRat 2) (line variance varianceRate step)))))
      (realBell (mul (selection.ofRat 2) upper) (sub (sub value mean) (mul meanRate step))) :=
    exp_monotone (neg_le_neg_iff.mpr (div_le_div_of_positive (mul_self_nonnegative _) scalePositive
      (mul_le_mul_nonnegative_left below (le_of_lt ofRat_two_positive))))
  have shifted := realBell_shift_le wideScalePositive (sub value mean) (mul meanRate step) moved
  rw [bell] at shifted
  have normalizerBelow : le (normalizer lower).toReal
      (normalizer (line variance varianceRate step)).toReal :=
    sqrt_monotone (NNReal.ofReal_monotone (mul_le_mul_nonnegative_left above
      (le_of_lt (mul_positive ofRat_two_positive pi_positive))))
  have reciprocal := inverse_le_inverse_of_positive lowerNormalizer normalizerBelow
  rw [div_eq_mul_inverse]
  refine le_trans (mul_le_mul_both (le_of_lt (exp_positive _))
    (inverse_nonnegative (le_of_lt (lt_of_lt_of_le lowerNormalizer normalizerBelow)))
    (le_trans wider shifted) reciprocal) (le_of_equal ?_)
  unfold lineEnvelope lineGrowth
  simp only [div_eq_mul_inverse]
  ac_rfl

/-- The log density's increment on the window is the step times the quadratic
bound. -/
public theorem abs_logDensity_sub_le {mean variance meanRate varianceRate lower upper reach
    step : selection.Carrier} (lowerPositive : lt zero lower)
    (baseAbove : le lower variance)
    (window : InLineWindow variance meanRate varianceRate lower upper reach step)
    (value : selection.Carrier) :
    le (abs (sub (logDensity (line mean meanRate step) (line variance varianceRate step) value)
        (logDensity mean variance value)))
      (mul (abs step)
        (lineIncrementBound meanRate varianceRate lower reach (sub value mean))) := by
  obtain ⟨above, _, moved⟩ := window
  have movingPositive := lt_of_lt_of_le lowerPositive above
  have varianceMove : sub (line variance varianceRate step) variance = mul varianceRate step :=
    add_sub_self variance (mul varianceRate step)
  unfold logDensity
  rw [shifted_center, increment_split _ _ _ _ (div (mul (sub value mean) (sub value mean))
    (mul (selection.ofRat 2) (line variance varianceRate step)))]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (abs_add_le _ _) (log_part_le lowerPositive baseAbove above varianceMove)) ?_
  refine le_trans (add_le_add (add_le_add
    (mean_part_le (mul_positive ofRat_two_positive movingPositive)
      (mul_positive ofRat_two_positive lowerPositive)
      (mul_le_mul_nonnegative_left above (le_of_lt ofRat_two_positive)) rfl moved)
    (variance_part_le lowerPositive baseAbove above varianceMove)) (le_refl _)) (le_of_equal ?_)
  unfold lineIncrementBound
  simp only [mul_add]

/-- The increment bound is nonnegative. -/
public theorem lineIncrementBound_nonnegative (meanRate varianceRate lower reach center :
    selection.Carrier) (lowerPositive : lt zero lower) (reachNonnegative : le zero reach) :
    le zero (lineIncrementBound meanRate varianceRate lower reach center) := by
  have doubledLower := le_of_lt (mul_positive ofRat_two_positive lowerPositive)
  have doubledSquare := mul_nonnegative (le_of_lt ofRat_two_positive) (mul_self_nonnegative lower)
  have quotient {numerator denominator : selection.Carrier} (numeratorNonnegative : le zero numerator)
      (denominatorNonnegative : le zero denominator) : le zero (div numerator denominator) := by
    rw [div_eq_mul_inverse]
    exact mul_nonnegative numeratorNonnegative (inverse_nonnegative denominatorNonnegative)
  exact add_nonnegative (add_nonnegative
    (mul_nonnegative (quotient (abs_nonnegative _) doubledLower)
      (add_nonnegative (add_nonnegative (abs_nonnegative _) (abs_nonnegative _)) reachNonnegative))
    (mul_nonnegative (quotient (abs_nonnegative _) doubledSquare) (mul_self_nonnegative center)))
    (quotient (abs_nonnegative _) doubledLower)

/-- The envelope is nonnegative. -/
public theorem lineEnvelope_nonnegative (mean lower upper reach value : selection.Carrier) :
    le zero (lineEnvelope mean lower upper reach value) := by
  have wide : le zero (normalizer (mul (selection.ofRat 2) upper)).toReal :=
    (normalizer (mul (selection.ofRat 2) upper)).property
  have narrow : le zero (normalizer lower).toReal := (normalizer lower).property
  have densityNonnegative : le zero (density mean (mul (selection.ofRat 2) upper) value).toReal :=
    (density mean (mul (selection.ofRat 2) upper) value).property
  unfold lineEnvelope lineGrowth
  rw [div_eq_mul_inverse]
  exact mul_nonnegative (mul_nonnegative (mul_nonnegative (le_of_lt (exp_positive _)) wide)
    (inverse_nonnegative narrow)) densityNonnegative

/-- The dominator is nonnegative. -/
public theorem lineDominator_nonnegative (mean meanRate varianceRate lower upper reach value :
    selection.Carrier) (lowerPositive : lt zero lower) (reachNonnegative : le zero reach) :
    le zero (lineDominator mean meanRate varianceRate lower upper reach value) :=
  mul_nonnegative (lineIncrementBound_nonnegative _ _ _ _ _ lowerPositive reachNonnegative)
    (add_nonnegative (lineEnvelope_nonnegative _ _ _ _ _) (lineEnvelope_nonnegative _ _ _ _ _))

/-- Every secant at step zero of the density along the line, with a step inside
the window, lies below the dominator. -/
public theorem line_secant_le_dominator {mean variance meanRate varianceRate lower upper reach
    radius : selection.Carrier} (lowerPositive : lt zero lower) (radiusPositive : lt zero radius)
    (window : ∀ step, lt (abs step) radius →
      InLineWindow variance meanRate varianceRate lower upper reach step)
    (value displacement : selection.Carrier) (nonzero : displacement ≠ zero)
    (small : lt (abs displacement) radius) :
    le (abs (secant (fun step =>
        (density (line mean meanRate step) (line variance varianceRate step) value).toReal)
        zero displacement))
      (lineDominator mean meanRate varianceRate lower upper reach value) := by
  have atZero := window zero (by rw [abs_zero]; exact radiusPositive)
  have envelopeZero := density_le_lineEnvelope (mean := mean) lowerPositive atZero value
  have envelopeMoved := density_le_lineEnvelope (mean := mean) lowerPositive
    (window displacement small) value
  have baseAbove : le lower variance := by
    have above := atZero.1
    rwa [line_at_zero] at above
  have basePositive := lt_of_lt_of_le lowerPositive baseAbove
  have movingPositive := lt_of_lt_of_le lowerPositive (window displacement small).1
  have increment := abs_logDensity_sub_le (mean := mean) lowerPositive baseAbove
    (window displacement small) value
  rw [line_at_zero, line_at_zero, density_exp mean variance value basePositive] at envelopeZero
  rw [density_exp _ _ value movingPositive] at envelopeMoved
  unfold secant
  simp only []
  rw [add_comm zero displacement, add_zero, line_at_zero, line_at_zero, density_exp mean variance value basePositive,
    density_exp _ _ value movingPositive, abs_div]
  have numerator := le_trans (abs_exp_sub_le _ _)
    (mul_le_mul_both (abs_nonnegative _)
      (add_nonnegative (le_of_lt (exp_positive _)) (le_of_lt (exp_positive _)))
      increment (add_le_add envelopeZero envelopeMoved))
  have stepPositive := abs_positive_of_nonzero nonzero
  refine le_trans (div_le_div_right stepPositive numerator) (le_of_equal ?_)
  unfold lineDominator
  rw [div_eq_mul_inverse]
  calc _ = mul (mul (lineIncrementBound meanRate varianceRate lower reach (sub value mean))
        (add (lineEnvelope mean lower upper reach value) (lineEnvelope mean lower upper reach value)))
        (mul (abs displacement) (inverse (abs displacement))) := by ac_rfl
    _ = _ := by rw [mul_inverse_cancel (nonzero_of_positive stepPositive), mul_one]

/-- The dominator is integrable against volume: its quadratic has every moment
it needs under the Gaussian law of variance twice the upper end. -/
public theorem lineDominator_hasRealIntegral (mean meanRate varianceRate lower upper reach :
    selection.Carrier) (upperPositive : lt zero upper) :
    ∃ dominatorValue : selection.Carrier,
      HasRealIntegral volume (lineDominator mean meanRate varianceRate lower upper reach)
        dominatorValue := by
  have widePositive := mul_positive ofRat_two_positive upperPositive
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
  have finite := ENNReal.finite_of_le
    (lintegral_mono (law mean (mul (selection.ofRat 2) upper)) pointwise)
    (absolute_centered_moment_finite mean (mul (selection.ofRat 2) upper) widePositive)
  obtain ⟨mass, massEqual⟩ := ENNReal.exists_finite_of_finite finite
  have absolute : HasRealIntegral (law mean (mul (selection.ofRat 2) upper))
      (fun x => abs (sub x mean)) (sub mass.toReal NNReal.zero.toReal) :=
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
  have constant (value : selection.Carrier) :
      HasRealIntegral (law mean (mul (selection.ofRat 2) upper)) (fun _ => value) value :=
    ⟨IntegralParts.const (law_isProbability mean (mul (selection.ofRat 2) upper) widePositive) value,
      IntegralParts.const_value _ _⟩
  have square := variance_expectation mean (mul (selection.ofRat 2) upper) widePositive
  have quadratic := ((((absolute.add absolute).add (constant reach)).smul
      (div (abs meanRate) (mul (selection.ofRat 2) lower))).add
    (square.smul (div (abs varianceRate) (mul (selection.ofRat 2) (mul lower lower))))).add
    (constant (div (abs varianceRate) (mul (selection.ofRat 2) lower)))
  have scaled := quadratic.smul (add (lineGrowth lower upper reach) (lineGrowth lower upper reach))
  have moved := HasRealIntegral.of_withDensity (measure := volume)
    (density := fun x => density mean (mul (selection.ofRat 2) upper) x)
    (density_measurable_slice mean (mul (selection.ofRat 2) upper)) scaled
  refine ⟨_, moved.congr (fun x => ?_)⟩
  unfold lineDominator lineIncrementBound lineEnvelope
  rw [← add_mul]
  ac_rfl

end

end Problib.Analysis.Gaussian
