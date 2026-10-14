module

public import Problib.Analysis.Logarithm.Derivative
public import Problib.Analysis.Real.MeanValue
public import Problib.Analysis.Real.PowerSeries.DerivativeCoefficients
public import Problib.Analysis.Real.PowerSeries.Reciprocal

/-! The logarithm is analytic on the positive reals.

Around a center `c > 0`, `log (c + d) = log c - Σ (-d / c)^n / n` near zero.
The series differentiates termwise, and its derived series is the reciprocal's
own series at `c`, so the series has the logarithm's derivative `1 / (c + d)`.
The difference of the two has zero derivative on an interval around zero and
vanishes at zero, so they agree there. Every center gets its own one-variable
series, so no series is ever recentered. Composition then carries the
logarithm through any positive analytic function.
-/

set_option autoImplicit false

namespace Problib.Analysis.Logarithm

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.SignedSeries
open Problib.Analysis.Real.PowerSeries

noncomputable section

/-- The coefficients of `log (center + d)` in powers of `d`. -/
@[expose] public def logCoefficients (center : selection.Carrier) :
    MultiIndex.carrier 1 → selection.Carrier :=
  fun index => match index 0 with
    | 0 => logIntegral center
    | count + 1 => mul (inverse (naturalScale (count + 1)))
        (neg (power (neg (inverse center)) (count + 1)))

private theorem one_le_naturalScale (count : Nat) : le one (naturalScale (count + 1)) := by
  have raised := add_le_add (le_refl one) (naturalScale_nonnegative count)
  rw [add_zero] at raised
  exact raised

private theorem naturalScale_nonzero (count : Nat) : naturalScale (count + 1) ≠ zero := by
  intro vanished
  have below := one_le_naturalScale count
  rw [vanished] at below
  exact lt_irrefl zero (lt_of_lt_of_le one_positive below)

private theorem inverse_naturalScale_le (count : Nat) :
    le (inverse (naturalScale (count + 1))) one := by
  have reversed := inverse_le_inverse_of_positive one_positive (one_le_naturalScale count)
  rwa [inverse_one] at reversed

/-- A one-variable displacement inside a ball around zero is below its radius. -/
public theorem displacement_below {radius : selection.Carrier}
    {displacement : FiniteVector.carrier 1}
    (inside : FiniteVector.ball (FiniteVector.zeroVector 1) radius displacement) :
    lt (abs (displacement 0)) radius := by
  have first := inside 0
  simpa only [FiniteVector.zeroVector, sub_zero] using first

private theorem line_ball {radius point : selection.Carrier} (small : lt (abs point) radius) :
    FiniteVector.ball (FiniteVector.zeroVector 1) radius (fun _ => point) := by
  intro _
  change lt (abs (sub point zero)) radius
  rw [sub_zero]
  exact small

/-- Each tail term of the logarithm's series is at most `|center|` times the
reciprocal's. -/
private theorem log_magnitude_le {center : selection.Carrier} (positive : lt zero center)
    (displacement : FiniteVector.carrier 1) (count : Nat) :
    le (tailMagnitudes (logCoefficients center) displacement count)
      (mul center (tailMagnitudes (reciprocalCoefficients center) displacement count)) := by
  have nonzero : center ≠ zero := fun vanished => by
    rw [vanished] at positive
    exact lt_irrefl zero positive
  let common := abs (mul (power (neg (inverse center)) (count + 1))
    (power (displacement 0) (count + 1)))
  have logTerm : tailMagnitudes (logCoefficients center) displacement count =
      mul (inverse (naturalScale (count + 1))) common := by
    unfold tailMagnitudes
    rw [shellMagnitude_line]
    change abs (mul (mul (inverse (naturalScale (count + 1)))
        (neg (power (neg (inverse center)) (count + 1))))
        (power (displacement 0) (count + 1))) = _
    rw [mul_assoc, abs_mul, neg_mul, abs_neg,
      abs_of_nonnegative (inverse_nonnegative (naturalScale_nonnegative _))]
  have reciprocalTerm : mul center
      (tailMagnitudes (reciprocalCoefficients center) displacement count) = common := by
    unfold tailMagnitudes
    rw [shellMagnitude_line]
    change mul center (abs (mul (mul (inverse center)
        (power (neg (inverse center)) (count + 1)))
        (power (displacement 0) (count + 1)))) = _
    rw [mul_assoc, abs_mul, abs_of_nonnegative
      (inverse_nonnegative positive.left), ← mul_assoc, mul_inverse_cancel nonzero,
      one_mul]
  rw [logTerm, reciprocalTerm]
  have raised := mul_le_mul_nonnegative_right (inverse_naturalScale_le count)
    (abs_nonnegative (mul (power (neg (inverse center)) (count + 1))
      (power (displacement 0) (count + 1))))
  rwa [one_mul] at raised

public theorem log_normal {center : selection.Carrier} (positive : lt zero center)
    {displacement : FiniteVector.carrier 1}
    (inside : lt (abs (displacement 0)) center) :
    NormallyConvergent (logCoefficients center) displacement := by
  have nonzero : center ≠ zero := fun vanished => by
    rw [vanished] at positive
    exact lt_irrefl zero positive
  have insideAbsolute : lt (abs (displacement 0)) (abs center) := by
    rw [abs_of_nonnegative positive.left]
    exact inside
  obtain ⟨bound, bounded⟩ := reciprocal_normal nonzero insideAbsolute
  refine ⟨mul center bound, fun count => ?_⟩
  refine le_trans (partialSum_le (log_magnitude_le positive displacement) count) ?_
  rw [partialSum_scale]
  exact mul_le_mul_nonnegative_left (bounded count) positive.left

/-- The local series of the logarithm at a positive center, on the ball whose
radius is the distance to zero. -/
@[expose] public def logSeries (center : selection.Carrier) (positive : lt zero center) :
    Convergent 1 where
  coefficients := logCoefficients center
  radius := center
  radiusPositive := positive
  normalOn := fun _ inside => log_normal positive (displacement_below inside)

/-- The termwise derivative of the logarithm's series at a center is the
reciprocal's series there. -/
public theorem logCoefficients_derivative (center : selection.Carrier) :
    partialDerivativeCoefficients 0 (logCoefficients center) =
      reciprocalCoefficients center := by
  funext index
  unfold partialDerivativeCoefficients
  have shifted : MultiIndex.addIndex index (MultiIndex.unitIndex 0) 0 = index 0 + 1 := by
    simp [MultiIndex.addIndex, MultiIndex.unitIndex]
  unfold logCoefficients
  rw [shifted]
  change mul (naturalScale (index 0 + 1)) (mul (inverse (naturalScale (index 0 + 1)))
      (neg (power (neg (inverse center)) (index 0 + 1)))) = _
  rw [← mul_assoc, mul_inverse_cancel (naturalScale_nonzero (index 0)), one_mul, power_succ,
    neg_mul, neg_neg]
  rfl

private theorem value_of_coefficients {first second : Convergent 1}
    (same : first.coefficients = second.coefficients) (displacement : FiniteVector.carrier 1)
    (firstInside : FiniteVector.ball (FiniteVector.zeroVector 1) first.radius displacement)
    (secondInside : FiniteVector.ball (FiniteVector.zeroVector 1) second.radius displacement) :
    value first displacement firstInside = value second displacement secondInside := by
  obtain ⟨coefficients, radius, radiusPositive, normalOn⟩ := first
  obtain ⟨otherCoefficients, otherRadius, otherPositive, otherNormal⟩ := second
  change coefficients = otherCoefficients at same
  subst same
  rfl

private theorem value_of_displacement (series : Convergent 1)
    {first second : FiniteVector.carrier 1} (same : first = second)
    (firstInside : FiniteVector.ball (FiniteVector.zeroVector 1) series.radius first)
    (secondInside : FiniteVector.ball (FiniteVector.zeroVector 1) series.radius second) :
    value series first firstInside = value series second secondInside := by
  subst same
  rfl

private theorem line_eq (point : FiniteVector.carrier 1) : point = fun _ => point 0 := by
  funext coordinate
  obtain ⟨index, bound⟩ := coordinate
  have single : index = 0 := by omega
  subst single
  rfl

private theorem replace_line (point : FiniteVector.carrier 1) (argument : selection.Carrier) :
    replaceCoordinate point 0 argument = fun _ => argument := by
  funext coordinate
  obtain ⟨index, bound⟩ := coordinate
  have single : index = 0 := by omega
  subst single
  simp [replaceCoordinate]

/-- The series read as a function of one real, through the coordinate slice at
zero. -/
private def slice (series : Convergent 1) : selection.Carrier → selection.Carrier :=
  coordinateValueAround series (fun _ => zero) 0

private theorem slice_shift (series : Convergent 1) (point : selection.Carrier) :
    coordinateValueAround series (fun _ => point) 0 =
      fun step => slice series (add point step) := by
  funext step
  unfold slice coordinateValueAround
  classical
  have same : replaceCoordinate (fun _ : Fin 1 => point) 0 (add point step) =
      replaceCoordinate (fun _ : Fin 1 => zero) 0 (add zero (add point step)) := by
    rw [replace_line, replace_line, zero_add]
  exact dite_congr (by rw [same]) (fun _ => value_of_displacement series same _ _)
    (fun _ => rfl)

private theorem slice_value (series : Convergent 1) {point : selection.Carrier}
    (inside : lt (abs point) series.radius) :
    slice series point = value series (fun _ => point) (line_ball inside) := by
  unfold slice
  have displaced : FiniteVector.ball (FiniteVector.zeroVector 1) series.radius
      (replaceCoordinate (fun _ => zero) 0 (add zero point)) := by
    rw [replace_line, zero_add]
    exact line_ball inside
  rw [coordinateValueAround_of_inside series (fun _ => zero) 0 point displaced]
  apply value_of_displacement
  rw [replace_line, zero_add]

private theorem hasDerivative_of_translate {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier}
    (shifted : HasDerivative (fun step => function (add point step)) zero derivative) :
    HasDerivative function point derivative := by
  intro epsilon positive
  rcases shifted epsilon positive with ⟨radius, radiusPositive, close⟩
  refine ⟨radius, radiusPositive, fun displacement nonzero small => ?_⟩
  have near := close displacement nonzero small
  simpa only [secant, zero_add, add_zero] using near

private theorem partialSum_zeros (count : Nat) :
    partialSum (fun _ => (zero : selection.Carrier)) count = zero := by
  induction count with
  | zero => exact partialSum_zero _
  | succ count previous => rw [partialSum_succ, previous, add_zero]

private theorem value_at_zero (series : Convergent 1)
    (inside : FiniteVector.ball (FiniteVector.zeroVector 1) series.radius (fun _ => zero)) :
    value series (fun _ => zero) inside = series.coefficients (MultiIndex.zeroIndex 1) := by
  have vanishing : tailTerms series.coefficients (fun _ => zero) = fun _ => zero := by
    funext count
    unfold tailTerms
    rw [shellTerm_line]
    change mul _ (power zero (count + 1)) = zero
    rw [power_succ, zero_mul, mul_zero]
  have summable : Summable (tailTerms series.coefficients (fun _ => zero)) :=
    summable_of_absolute_bound (series.absoluteOn (fun _ => zero) inside)
  have converges : ConvergesTo (partialSum (tailTerms series.coefficients (fun _ => zero)))
      zero := by
    rw [vanishing, show partialSum (fun _ => (zero : selection.Carrier)) = fun _ => zero from
      funext partialSum_zeros]
    exact converges_to_const zero
  unfold value
  rw [sum_eq_of_converges _ summable converges, add_zero]

/-- The radius on which the logarithm's series is shown equal to the logarithm:
a quarter of the distance to zero, where termwise differentiation holds. -/
@[expose] public def logRadius (center : selection.Carrier) : selection.Carrier :=
  mul (half one) (half center)

private theorem half_lt_self {value : selection.Carrier} (positive : lt zero value) :
    lt (half value) value := by
  have raised := add_lt_add_left (half value) (half_positive positive)
  rwa [add_zero, add_half] at raised

public theorem logRadius_positive {center : selection.Carrier} (positive : lt zero center) :
    lt zero (logRadius center) :=
  mul_positive (half_positive one_positive) (half_positive positive)

public theorem logRadius_lt {center : selection.Carrier} (positive : lt zero center) :
    lt (logRadius center) center := by
  have shrunk := mul_le_mul_nonnegative_right (le_of_lt (half_lt_self one_positive))
    (half_positive positive).left
  rw [one_mul] at shrunk
  exact lt_of_le_of_lt shrunk (half_lt_self positive)

private theorem shifted_positive {center point : selection.Carrier}
    (positive : lt zero center) (above : lt (neg (logRadius center)) point) :
    lt zero (add center point) := by
  have below : lt (neg center) point :=
    lt_trans (neg_lt_neg_iff.mpr (logRadius_lt positive)) above
  have shifted := add_lt_add_left center below
  rwa [add_neg] at shifted

/-- On the quarter ball, the logarithm's series sums to the logarithm. -/
private theorem slice_eq_log {center : selection.Carrier} (positive : lt zero center)
    {point : selection.Carrier} (inside : lt (abs point) (logRadius center)) :
    slice (logSeries center positive) point = logIntegral (add center point) := by
  have nonzero : center ≠ zero := fun vanished => by
    rw [vanished] at positive
    exact lt_irrefl zero positive
  let series := logSeries center positive
  let difference := fun step => sub (logIntegral (add center step)) (slice series step)
  have flat : ∀ step, lt (neg (logRadius center)) step → lt step (logRadius center) →
      HasDerivative difference step zero := by
    intro step above below
    have small : lt (abs step) (logRadius center) := abs_lt.mpr ⟨above, below⟩
    have derivedInside : FiniteVector.ball (FiniteVector.zeroVector 1)
        (partialDerivativeSeries series 0).radius (fun _ => step) := line_ball small
    have termwise := coordinateValueAround_has_derivative_partial_series series
      (fun _ => step) 0 derivedInside
    rw [slice_shift] at termwise
    have reciprocalInside : FiniteVector.ball (FiniteVector.zeroVector 1)
        (reciprocalSeries center nonzero).radius (fun _ => step) := by
      apply line_ball
      change lt (abs step) (abs center)
      rw [abs_of_nonnegative positive.left]
      exact lt_trans small (logRadius_lt positive)
    rw [value_of_coefficients (logCoefficients_derivative center) (fun _ => step)
      derivedInside reciprocalInside, reciprocalSeries_value] at termwise
    have seriesDerivative := hasDerivative_of_translate termwise
    have shiftDerivative : HasDerivative (fun value => add center value) step one := by
      have summed := hasDerivative_add (hasDerivative_const center step)
        (hasDerivative_identity step)
      rwa [zero_add] at summed
    have logDerivative := hasDerivative_comp (outer := logIntegral)
      (hasDerivative_log (shifted_positive positive above)) shiftDerivative
    rw [mul_one] at logDerivative
    have both := hasDerivative_sub logDerivative seriesDerivative
    rwa [sub_self] at both
  have radiusPositive := logRadius_positive positive
  have zeroAbove : lt (neg (logRadius center)) zero := by
    have negated := neg_lt_neg_iff.mpr radiusPositive
    rwa [neg_zero] at negated
  have constant := eq_of_hasDerivative_zero_on flat zeroAbove radiusPositive
    (abs_lt.mp inside).1 (abs_lt.mp inside).2
  have atZero : difference zero = zero := by
    change sub (logIntegral (add center zero)) (slice series zero) = zero
    have zeroInside : lt (abs zero) series.radius := by
      rw [abs_zero]
      exact positive
    rw [slice_value series zeroInside, value_at_zero, add_zero]
    exact sub_self _
  rw [atZero] at constant
  have atPoint : sub (logIntegral (add center point)) (slice series point) = zero :=
    constant.symm
  rw [← sub_add_cancel (logIntegral (add center point)) (slice series point), atPoint,
    zero_add]

/-- The logarithm's local series, on the quarter ball where it is the
logarithm. -/
@[expose, implicit_reducible] public def logLocalSeries (center : selection.Carrier) (positive : lt zero center) :
    Convergent 1 :=
  restrictRadius (logSeries center positive) (logRadius center) (logRadius_positive positive)
    (le_of_lt (logRadius_lt positive))

public theorem logLocalSeries_value {center : selection.Carrier} (positive : lt zero center)
    (displacement : FiniteVector.carrier 1)
    (inside : FiniteVector.ball (FiniteVector.zeroVector 1)
      (logLocalSeries center positive).radius displacement) :
    value (logLocalSeries center positive) displacement inside =
      logIntegral (add center (displacement 0)) := by
  have small : lt (abs (displacement 0)) (logRadius center) := displacement_below inside
  have seriesSmall : lt (abs (displacement 0)) (logSeries center positive).radius :=
    lt_trans small (logRadius_lt positive)
  rw [← slice_eq_log positive small, slice_value _ seriesSmall]
  unfold logLocalSeries
  rw [restrictRadius_value]
  exact value_of_displacement _ (line_eq displacement) _ _

/-- A point closer to a positive center than the center is to zero is
positive. -/
public theorem positive_near {center neighbor : selection.Carrier}
    (close : lt (abs (sub neighbor center)) center) : lt zero neighbor := by
  have shifted := add_lt_add_left center (abs_lt.mp close).1
  rwa [add_neg, add_sub_cancel] at shifted

/-- The vectors with a positive coordinate form an open set. -/
public theorem is_open_positive {dimension : Nat} (coordinate : Fin dimension) :
    FiniteVector.IsOpen
      (fun point : FiniteVector.carrier dimension => lt zero (point coordinate)) :=
  fun point positive => ⟨point coordinate, positive,
    fun _ inside => positive_near (inside coordinate)⟩

/-- The logarithm is analytic on the positive reals. -/
public theorem analytic_on_log :
    AnalyticOn (fun point : FiniteVector.carrier 1 => lt zero (point 0))
      (fun point => logIntegral (point 0)) := by
  refine ⟨is_open_positive 0, fun center member => ?_⟩
  refine ⟨logLocalSeries (center 0) member, fun point inside => ?_, fun point inside => ?_⟩
  · exact positive_near (lt_trans (inside 0) (logRadius_lt member))
  · rw [logLocalSeries_value]
    change logIntegral (point 0) =
      logIntegral (add (center 0) (sub (point 0) (center 0)))
    rw [add_sub_cancel]

/-- The logarithm of a positive analytic function is analytic. -/
public theorem analytic_on_log_comp {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    (positive : ∀ point, region point → lt zero (function point)) :
    AnalyticOn region (fun point => logIntegral (function point)) :=
  analytic_on_comp (inner := fun point _ => function point)
    analytic.left (fun _ => analytic) analytic_on_log positive

end

end Problib.Analysis.Logarithm
