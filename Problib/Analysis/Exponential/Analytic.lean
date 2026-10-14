module

public import Problib.Analysis.Exponential.Series
public import Problib.Analysis.Real.PowerSeries.Reciprocal

/-! The exponential is analytic everywhere.

Around a center `c`, `exp (c + d) = exp c · Σ d^n / n!` for every `d`, by the
product law and the factorial series. Every center gets its own one-variable
series of radius one, so no series is ever recentered. Composition then
carries the exponential through any analytic function.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.SignedSeries
open Problib.Analysis.Real.PowerSeries

noncomputable section

private theorem factorialTerm_power (value : selection.Carrier) :
    ∀ count, mul (factorialTerm one count) (power value count) =
      factorialTerm value count
  | 0 => by rw [factorialTerm_zero, factorialTerm_zero, power_zero, one_mul]
  | count + 1 => by
      rw [factorialTerm_succ, factorialTerm_succ, power_succ,
        ← factorialTerm_power value count, div_eq_mul_inverse, div_eq_mul_inverse,
        one_mul]
      ac_rfl

private theorem partialSum_tail_le {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index)) :
    ∀ length, le (partialSum (fun index => values (index + 1)) length)
      (partialSum values (length + 1))
  | 0 => by
      rw [partialSum_zero, partialSum_succ, partialSum_zero, zero_add]
      exact nonnegative 0
  | length + 1 => by
      rw [partialSum_succ, partialSum_succ values (length + 1)]
      exact add_le_add (partialSum_tail_le nonnegative length) (le_refl _)

/-- The coefficients of `exp (center + d)` in powers of `d`. -/
@[expose] public def expCoefficients (center : selection.Carrier) :
    MultiIndex.carrier 1 → selection.Carrier :=
  fun index => mul (exp center) (factorialTerm one (index 0))

private theorem exp_tail (center : selection.Carrier)
    (displacement : FiniteVector.carrier 1) :
    tailTerms (expCoefficients center) displacement =
      fun count => mul (exp center) (factorialTerm (displacement 0) (count + 1)) := by
  funext count
  unfold tailTerms
  rw [shellTerm_line]
  unfold expCoefficients lineIndex
  rw [mul_assoc, factorialTerm_power]

/-- The exponential series at any center converges normally everywhere. -/
public theorem exp_normal (center : selection.Carrier)
    (displacement : FiniteVector.carrier 1) :
    NormallyConvergent (expCoefficients center) displacement := by
  let magnitude := abs (displacement 0)
  have magnitudeNonnegative : le zero magnitude := abs_nonnegative _
  have termsNonnegative := factorialTerm_nonnegative magnitudeNonnegative
  refine ⟨mul (exp center) (sum (factorialTerm magnitude)
    (factorial_summable magnitude)), fun count => ?_⟩
  have magnitudes : tailMagnitudes (expCoefficients center) displacement =
      fun index => mul (exp center) (factorialTerm magnitude (index + 1)) := by
    funext index
    unfold tailMagnitudes
    rw [shellMagnitude_line]
    change abs (mul (mul (exp center) (factorialTerm one (index + 1)))
        (power (displacement 0) (index + 1))) = _
    rw [mul_assoc, factorialTerm_power, abs_mul,
      abs_of_nonnegative (le_of_lt (exp_positive center))]
    rw [abs_factorialTerm]
  rw [magnitudes, partialSum_scale]
  apply mul_le_mul_nonnegative_left _ (le_of_lt (exp_positive center))
  exact le_trans (partialSum_tail_le termsNonnegative count)
    (partialSum_le_sum_nonnegative termsNonnegative
      (factorial_summable magnitude) (count + 1))

/-- The local series of the exponential at a center, on the unit ball. -/
@[expose] public def expSeries (center : selection.Carrier) : Convergent 1 where
  coefficients := expCoefficients center
  radius := one
  radiusPositive := one_positive
  normalOn := fun displacement _ => exp_normal center displacement

public theorem expSeries_value (center : selection.Carrier)
    (displacement : FiniteVector.carrier 1)
    (inside : FiniteVector.ball (FiniteVector.zeroVector 1)
      (expSeries center).radius displacement) :
    value (expSeries center) displacement inside =
      exp (add center (displacement 0)) := by
  let terms := factorialTerm (displacement 0)
  let certificate := factorial_summable (displacement 0)
  have tail := partialSum_tail_converges terms certificate 1
  have firstPartial : partialSum terms 1 = one := by
    rw [partialSum_succ, partialSum_zero, zero_add]
    exact factorialTerm_zero _
  rw [firstPartial] at tail
  have shifted : (fun index => terms (1 + index)) =
      (fun index => terms (index + 1)) := by
    funext index
    rw [Nat.add_comm]
  rw [shifted] at tail
  have scaled := converges_to_scale (exp center) tail
  have partialEqual : (fun count => mul (exp center)
      (partialSum (fun index => terms (index + 1)) count)) =
      partialSum (tailTerms (expCoefficients center) displacement) := by
    funext count
    rw [exp_tail, partialSum_scale]
  rw [partialEqual] at scaled
  have tailSum := sum_eq_of_converges _
    (summable_of_absolute_bound
      ((expSeries center).absoluteOn displacement inside))
    scaled
  unfold value
  rw [tailSum]
  change add (expCoefficients center (MultiIndex.zeroIndex 1)) _ = _
  have constantTerm : expCoefficients center (MultiIndex.zeroIndex 1) =
      exp center := by
    unfold expCoefficients
    rw [show MultiIndex.zeroIndex 1 0 = 0 from rfl, factorialTerm_zero, mul_one]
  rw [constantTerm, exp_add, exp_eq_sum (displacement 0), mul_sub, mul_one,
    add_sub_cancel]

/-- The exponential is analytic on the whole line. -/
public theorem analytic_on_exp :
    AnalyticOn (fun _ : FiniteVector.carrier 1 => True)
      (fun point => exp (point 0)) := by
  refine ⟨FiniteVector.is_open_univ 1, fun center _ => ?_⟩
  refine ⟨expSeries (center 0), fun _ _ => True.intro, ?_⟩
  intro point inside
  rw [expSeries_value]
  change exp (point 0) = exp (add (center 0) (sub (point 0) (center 0)))
  rw [add_sub_cancel]

/-- The exponential of an analytic function is analytic. -/
public theorem analytic_on_exp_comp {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function) :
    AnalyticOn region (fun point => exp (function point)) :=
  analytic_on_comp (inner := fun point _ => function point)
    analytic.left (fun _ => analytic) analytic_on_exp (fun _ _ => True.intro)

end

end Problib.Analysis
