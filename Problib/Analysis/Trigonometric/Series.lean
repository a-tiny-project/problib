module

public import Problib.Analysis.Exponential.Series
public import Problib.Analysis.Real.PowerSeries.Reciprocal
public import Problib.Analysis.Real.PowerSeries.AnalyticDerivative
import Problib.Real.Grind

/-! Factorial series with bounded weights.

A weight is a coefficient sequence `w` with `|wₙ| ≤ B` for one bound `B`. Its
series `Σ wₙ xⁿ / n!` converges absolutely at every `x`, because each term is
at most `B` times the factorial term of `|x|`. Sine and cosine are two such
series, and the derivative of one is the series of the shifted weights
`n ↦ wₙ₊₁`.

The derivative is read off the library's power-series derivative: on the line,
the series is a convergent one-variable power series of any radius, and its
formal coordinate derivative has coefficients `(n + 1) · wₙ₊₁ / (n + 1)!`,
which are the shifted weights' factorial coefficients. The same local series,
at radius one, is the analytic witness.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Trigonometric

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.SignedSeries
open Problib.Analysis.Real.PowerSeries

noncomputable section

/-- A coefficient sequence with one bound on every magnitude. -/
public structure Weight where
  values : Nat → selection.Carrier
  bound : selection.Carrier
  bounded : ∀ index, le (abs (values index)) bound

public theorem Weight.bound_nonnegative (weight : Weight) : le zero weight.bound :=
  le_trans (abs_nonnegative _) (weight.bounded 0)

/-- The weights one place later, those of the derivative. -/
@[expose] public def Weight.shift (weight : Weight) : Weight where
  values := fun index => weight.values (index + 1)
  bound := weight.bound
  bounded := fun index => weight.bounded (index + 1)

/-- The weights `a · v + b · u`, one index at a time. -/
@[expose] public def Weight.combine (first : selection.Carrier) (left : Weight)
    (second : selection.Carrier) (right : Weight) : Weight where
  values := fun index =>
    add (mul first (left.values index)) (mul second (right.values index))
  bound := add (mul (abs first) left.bound) (mul (abs second) right.bound)
  bounded := fun index => by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul_nonnegative_left (left.bounded index) (abs_nonnegative first))
      (mul_le_mul_nonnegative_left (right.bounded index) (abs_nonnegative second))

/-- The terms `wₙ · xⁿ / n!`. -/
@[expose] public def terms (weight : Weight) (point : selection.Carrier) :
    Nat → selection.Carrier :=
  fun index => mul (weight.values index) (factorialTerm point index)

private theorem abs_terms_le (weight : Weight) (point : selection.Carrier)
    (index : Nat) :
    le (abs (terms weight point index))
      (mul weight.bound (factorialTerm (abs point) index)) := by
  unfold terms
  rw [abs_mul, abs_factorialTerm]
  exact mul_le_mul_nonnegative_right (weight.bounded index)
    (factorialTerm_nonnegative (abs_nonnegative point) index)

public theorem terms_summable (weight : Weight) (point : selection.Carrier) :
    Summable (terms weight point) := by
  refine summable_of_majorant (abs_terms_le weight point)
    ⟨mul weight.bound (sum (factorialTerm (abs point))
      (factorial_summable (abs point))), fun count => ?_⟩
  rw [partialSum_scale]
  exact mul_le_mul_nonnegative_left
    (partialSum_le_sum_nonnegative
      (factorialTerm_nonnegative (abs_nonnegative point))
      (factorial_summable (abs point)) count)
    weight.bound_nonnegative

/-- The weighted factorial series `Σ wₙ xⁿ / n!`. -/
@[expose] public def weighted (weight : Weight) (point : selection.Carrier) :
    selection.Carrier :=
  sum (terms weight point) (terms_summable weight point)

/-- The series reads only the weights' values, not their bound. -/
public theorem weighted_congr {first second : Weight}
    (same : first.values = second.values) (point : selection.Carrier) :
    weighted first point = weighted second point := by
  unfold weighted
  apply sum_congr
  funext index
  unfold terms
  rw [same]

public theorem weighted_zero (weight : Weight) :
    weighted weight zero = weight.values 0 := by
  apply sum_eq_of_converges
  intro epsilon positive
  refine ⟨1, fun count later => ?_⟩
  have constant : ∀ length, partialSum (terms weight zero) (length + 1) =
      weight.values 0 := by
    intro length
    induction length with
    | zero =>
        rw [partialSum_succ, partialSum_zero, zero_add]
        change mul (weight.values 0) one = _
        rw [mul_one]
    | succ length previous =>
        rw [partialSum_succ, previous]
        change add _ (mul _ (div (mul zero _) _)) = _
        rw [zero_mul, zero_div, mul_zero, add_zero]
  obtain ⟨length, rfl⟩ : ∃ length, count = length + 1 := ⟨count - 1, by omega⟩
  rw [constant, sub_self, abs_zero]
  exact positive

public theorem weighted_combine (first : selection.Carrier) (left : Weight)
    (second : selection.Carrier) (right : Weight) (point : selection.Carrier) :
    weighted (Weight.combine first left second right) point =
      add (mul first (weighted left point)) (mul second (weighted right point)) := by
  unfold weighted
  rw [← sum_scale first (terms_summable left point),
    ← sum_scale second (terms_summable right point),
    ← sum_add (summable_scale first (terms_summable left point))
      (summable_scale second (terms_summable right point))]
  apply sum_congr
  funext index
  unfold terms Weight.combine
  simp only [add_mul, mul_assoc]

/-! ### The series on the line -/

private theorem factorialTerm_power (value : selection.Carrier) :
    ∀ count, mul (factorialTerm one count) (power value count) =
      factorialTerm value count
  | 0 => by rw [factorialTerm_zero, factorialTerm_zero, power_zero, one_mul]
  | count + 1 => by
      rw [factorialTerm_succ, factorialTerm_succ, power_succ,
        ← factorialTerm_power value count, div_eq_mul_inverse, div_eq_mul_inverse,
        one_mul]
      ac_rfl

/-- The one-variable coefficients `wₙ / n!` of a weight. -/
@[expose] public def lineCoefficients (weight : Weight) :
    MultiIndex.carrier 1 → selection.Carrier :=
  fun index => mul (weight.values (index 0)) (factorialTerm one (index 0))

section Line

variable (coefficients : MultiIndex.carrier 1 → selection.Carrier) (weight : Weight)
  (agree : ∀ count, coefficients (lineIndex count) =
    mul (weight.values count) (factorialTerm one count))

include agree

private theorem line_term (displacement : FiniteVector.carrier 1) (count : Nat) :
    shellTerm coefficients displacement count =
      terms weight (displacement 0) count := by
  rw [shellTerm_line, agree, mul_assoc, factorialTerm_power]
  rfl

private theorem line_magnitude (displacement : FiniteVector.carrier 1) (count : Nat) :
    shellMagnitude coefficients displacement count =
      abs (terms weight (displacement 0) count) := by
  rw [shellMagnitude_line, agree, mul_assoc, factorialTerm_power]
  rfl

/-- Coefficients that are a weight's on the line converge normally everywhere. -/
public theorem line_normal (displacement : FiniteVector.carrier 1) :
    NormallyConvergent coefficients displacement := by
  let magnitude := abs (displacement 0)
  let majorant := fun index => mul weight.bound (factorialTerm magnitude index)
  have majorantNonnegative : ∀ index, le zero (majorant index) := fun index =>
    mul_nonnegative weight.bound_nonnegative
      (factorialTerm_nonnegative (abs_nonnegative _) index)
  have majorantSummable : Summable majorant :=
    summable_scale weight.bound (factorial_summable magnitude)
  refine ⟨sum majorant majorantSummable, fun count => ?_⟩
  have magnitudes : tailMagnitudes coefficients displacement =
      fun index => abs (terms weight (displacement 0) (1 + index)) := by
    funext index
    unfold tailMagnitudes
    rw [line_magnitude coefficients weight agree, Nat.add_comm]
  rw [magnitudes]
  refine le_trans (partialSum_le
    (fun index => abs_terms_le weight (displacement 0) (1 + index)) count) ?_
  refine le_trans ?_ (partialSum_le_sum_nonnegative majorantNonnegative
    majorantSummable (1 + count))
  rw [partialSum_append majorant 1 count]
  have first : le zero (partialSum majorant 1) := by
    rw [partialSum_succ, partialSum_zero, zero_add]
    exact majorantNonnegative 0
  have shifted := add_le_add first
    (le_refl (partialSum (fun index => majorant (1 + index)) count))
  rwa [zero_add] at shifted

omit agree in
/-- A convergent series whose coefficients are a weight's on the line has the
weighted series as its value. -/
public theorem line_value (series : Convergent 1)
    (seriesAgree : ∀ count, series.coefficients (lineIndex count) =
      mul (weight.values count) (factorialTerm one count))
    (displacement : FiniteVector.carrier 1)
    (inside : FiniteVector.ball (FiniteVector.zeroVector 1) series.radius
      displacement) :
    value series displacement inside = weighted weight (displacement 0) := by
  let point := displacement 0
  have tail := partialSum_tail_converges (terms weight point)
    (terms_summable weight point) 1
  have shiftedTerms : (fun index => terms weight point (1 + index)) =
      tailTerms series.coefficients displacement := by
    funext index
    unfold tailTerms
    rw [line_term series.coefficients weight seriesAgree, Nat.add_comm]
  rw [shiftedTerms] at tail
  have tailSum := sum_eq_of_converges _
    (summable_of_absolute_bound (series.absoluteOn displacement inside)) tail
  unfold value
  rw [tailSum]
  have constant : series.coefficients (MultiIndex.zeroIndex 1) =
      partialSum (terms weight point) 1 := by
    rw [partialSum_succ, partialSum_zero, zero_add]
    exact (seriesAgree 0).trans (by rw [factorialTerm_zero]; rfl)
  rw [constant, add_comm, sub_add_cancel]
  rfl

end Line

/-- The local series of a weight around zero, at any positive radius. -/
@[expose] public def weightedSeries (weight : Weight) (radius : selection.Carrier)
    (positive : lt zero radius) : Convergent 1 where
  coefficients := lineCoefficients weight
  radius := radius
  radiusPositive := positive
  normalOn := fun displacement _ =>
    line_normal (lineCoefficients weight) weight (fun _ => rfl) displacement

public theorem weightedSeries_value (weight : Weight) (radius : selection.Carrier)
    (positive : lt zero radius) (displacement : FiniteVector.carrier 1)
    (inside : FiniteVector.ball (FiniteVector.zeroVector 1)
      (weightedSeries weight radius positive).radius displacement) :
    value (weightedSeries weight radius positive) displacement inside =
      weighted weight (displacement 0) :=
  line_value weight (weightedSeries weight radius positive) (fun _ => rfl)
    displacement inside

/-! ### The derivative -/

private theorem naturalScale_eq : ∀ count : Nat,
    naturalScale count = selection.ofRat ((count : Nat) : Rat)
  | 0 => ofRat_zero.symm
  | count + 1 => by
      change add one (naturalScale count) = _
      rw [naturalScale_eq count, Rat.natCast_add, ofRat_add,
        show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one, add_comm]

private theorem natural_nonzero (count : Nat) :
    selection.ofRat (((count + 1 : Nat)) : Rat) ≠ zero := by
  intro vanished
  have embedded := (ofRat_lt_iff 0 ((count + 1 : Nat) : Rat)).mpr
    (Rat.natCast_pos.mpr (Nat.succ_pos count))
  rw [ofRat_zero, vanished] at embedded
  exact lt_irrefl zero embedded

/-- Differentiating the line coefficients gives the shifted weight's. -/
private theorem derivative_line (weight : Weight) (count : Nat) :
    partialDerivativeCoefficients 0 (lineCoefficients weight) (lineIndex count) =
      mul (weight.shift.values count) (factorialTerm one count) := by
  have raised : MultiIndex.addIndex (lineIndex count) (MultiIndex.unitIndex 0) 0 =
      count + 1 := by
    simp [MultiIndex.addIndex, MultiIndex.unitIndex, lineIndex]
  unfold partialDerivativeCoefficients lineCoefficients
  rw [raised]
  change mul (naturalScale (count + 1))
      (mul (weight.values (count + 1)) (factorialTerm one (count + 1))) =
    mul (weight.values (count + 1)) (factorialTerm one count)
  rw [naturalScale_eq, factorialTerm_succ, one_mul, ← mul_assoc,
    mul_comm (selection.ofRat _) (weight.values (count + 1)), mul_assoc,
    mul_div_cancel _ (natural_nonzero count)]

/-- Weighted factorial series differentiate termwise: the derivative is the
series of the shifted weights. -/
public theorem hasDerivative_weighted (weight : Weight) (point : selection.Carrier) :
    HasDerivative (weighted weight) point (weighted weight.shift point) := by
  let margin := add (abs point) one
  have marginPositive : lt zero margin := by
    have shifted := add_le_add (abs_nonnegative point) (le_refl one)
    rw [zero_add] at shifted
    exact lt_of_lt_of_le one_positive shifted
  let radius := mul (selection.ofRat 4) margin
  have radiusPositive : lt zero radius :=
    mul_positive (ofRat_lt_iff 0 4 |>.mpr (by decide) |> fun h => by
      rwa [ofRat_zero] at h) marginPositive
  let series := weightedSeries weight radius radiusPositive
  let center : FiniteVector.carrier 1 := fun _ => point
  have shrunk : mul (half one) (half radius) = margin := by
    have scaled : ∀ value : selection.Carrier,
        mul (half one) (half (mul (selection.ofRat 4) value)) = value := by
      intro value
      unfold half two
      real_grind
    exact scaled margin
  have centerInside : FiniteVector.ball (FiniteVector.zeroVector 1)
      (partialDerivativeSeries series 0).radius center := by
    intro coordinate
    rw [partialDerivativeSeries_radius]
    change lt (abs (sub point zero)) (mul (half one) (half radius))
    rw [sub_zero, shrunk]
    have shifted := add_lt_add_left (abs point) one_positive
    rwa [add_zero] at shifted
  have derivative := coordinateValueAround_has_derivative_partial_series series
    center 0 centerInside
  rw [line_value weight.shift (partialDerivativeSeries series 0)
    (derivative_line weight) center centerInside] at derivative
  have near : NearZero fun step =>
      coordinateValueAround series center 0 step = weighted weight (add point step) := by
    refine ⟨one, one_positive, fun step small => ?_⟩
    have moved : replaceCoordinate center 0 (add (center 0) step) =
        fun _ => add point step := by
      funext coordinate
      simp [replaceCoordinate, center, Fin.fin_one_eq_zero coordinate]
    have inside : FiniteVector.ball (FiniteVector.zeroVector 1) series.radius
        (replaceCoordinate center 0 (add (center 0) step)) := by
      rw [moved]
      intro coordinate
      change lt (abs (sub (add point step) zero)) radius
      rw [sub_zero]
      refine lt_of_le_of_lt (abs_add_le point step) ?_
      have below : lt (add (abs point) (abs step)) margin :=
        add_lt_add_left (abs point) small
      refine lt_trans below ?_
      have split : ∀ value : selection.Carrier, mul (selection.ofRat 4) value =
          add value (mul (selection.ofRat 3) value) := by
        intro value
        real_grind
      change lt margin (mul (selection.ofRat 4) margin)
      rw [split]
      have extra := add_lt_add_left margin
        (mul_positive (ofRat_lt_iff 0 3 |>.mpr (by decide) |> fun h => by
          rwa [ofRat_zero] at h) marginPositive)
      rwa [add_zero] at extra
    show coordinateValueAround series center 0 step = weighted weight (add point step)
    rw [coordinateValueAround_of_inside series center 0 step inside,
      weightedSeries_value]
    change weighted weight ((replaceCoordinate center 0 (add (center 0) step)) 0) = _
    rw [moved]
  have translated := HasDerivative.congr_near_zero near derivative
  intro epsilon positive
  rcases translated epsilon positive with ⟨gap, gapPositive, close⟩
  refine ⟨gap, gapPositive, fun step nonzero small => ?_⟩
  simpa only [secant, zero_add, add_zero] using close step nonzero small

end

end Problib.Analysis.Trigonometric
