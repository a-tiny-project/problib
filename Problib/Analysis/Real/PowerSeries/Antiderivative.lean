module

public import Problib.Analysis.Real.PowerSeries.Identity
public import Problib.Analysis.Real.PowerSeries.Reciprocal
public import Problib.Analysis.Real.Composition
public import Problib.Analysis.Real.MeanValue
import Problib.Real.Grind

/-! A function of one coordinate whose derivative is analytic is analytic.

A function defined by an integral, such as the arctangent or the Gaussian
distribution function, has an analytic derivative but no closed series at
every center. At each center the derivative's local series `Σ aₙ dⁿ` is
integrated term by term, to `F c + Σ aₙ dⁿ⁺¹ / (n + 1)`. Its coefficients are
smaller than the derivative's after one shift, so it converges on the same
ball. Its formal derivative series has the derivative's coefficients, and the
library's termwise differentiation shows that its value differentiates to the
derivative on a smaller ball. There the function and the integrated series
have the same derivative and agree at the center, so the zero-derivative
theorem makes them equal.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.SignedSeries

noncomputable section

/-- The coefficients of `constant + Σ aₙ dⁿ⁺¹ / (n + 1)` for derivative
coefficients `a`. -/
@[expose] public def integratedCoefficients (constant : selection.Carrier)
    (coefficients : MultiIndex.carrier 1 → selection.Carrier) :
    MultiIndex.carrier 1 → selection.Carrier :=
  fun index => match index 0 with
    | 0 => constant
    | count + 1 => div (coefficients (lineIndex count)) (naturalScale (count + 1))

private theorem line_index_eq (index : MultiIndex.carrier 1) : index = lineIndex (index 0) := by
  funext coordinate
  rw [fin_one_eq_zero coordinate]
  rfl

/-- Each integrated tail magnitude is at most the displacement's size times the
derivative series' magnitude one degree lower. -/
private theorem integrated_magnitude_le (constant : selection.Carrier)
    (coefficients : MultiIndex.carrier 1 → selection.Carrier)
    (displacement : FiniteVector.carrier 1) (count : Nat) :
    le (tailMagnitudes (integratedCoefficients constant coefficients) displacement count)
      (mul (abs (displacement 0)) (shellMagnitude coefficients displacement count)) := by
  unfold tailMagnitudes
  rw [shellMagnitude_line, shellMagnitude_line]
  have scalePositive := naturalScale_succ_positive count
  have scaleNonzero := nonzero_of_positive scalePositive
  have scaleAbove : le one (naturalScale (count + 1)) := by
    change le one (add one (naturalScale count))
    have := naturalScale_nonnegative count
    real_grind
  have factored : mul (integratedCoefficients constant coefficients (lineIndex (count + 1)))
      (power (displacement 0) (count + 1)) =
      mul (mul (coefficients (lineIndex count)) (power (displacement 0) count))
        (mul (displacement 0) (inverse (naturalScale (count + 1)))) := by
    change mul (div (coefficients (lineIndex count)) (naturalScale (count + 1)))
      (mul (displacement 0) (power (displacement 0) count)) = _
    rw [div_eq_mul_inverse]
    real_grind
  have inverseNonnegative := (inverse_of_positive_positive scalePositive).1
  have inverseBelow : le (inverse (naturalScale (count + 1))) one := by
    simpa only [inverse_one] using inverse_le_inverse_of_positive one_positive scaleAbove
  rw [factored, abs_mul (mul (coefficients (lineIndex count)) (power (displacement 0) count)),
    abs_mul (displacement 0), abs_of_nonnegative inverseNonnegative]
  have shrunk := mul_le_mul_nonnegative_left inverseBelow (abs_nonnegative (displacement 0))
  have scaled := mul_le_mul_nonnegative_left shrunk
    (abs_nonnegative (mul (coefficients (lineIndex count)) (power (displacement 0) count)))
  real_grind

private theorem integrated_partialSum_le (constant : selection.Carrier)
    (coefficients : MultiIndex.carrier 1 → selection.Carrier)
    (displacement : FiniteVector.carrier 1) :
    ∀ count, le (partialSum (tailMagnitudes (integratedCoefficients constant coefficients)
        displacement) (count + 1))
      (mul (abs (displacement 0)) (add (shellMagnitude coefficients displacement 0)
        (partialSum (tailMagnitudes coefficients displacement) count)))
  | 0 => by
      rw [partialSum_succ, partialSum_zero, partialSum_zero, zero_add, add_zero]
      exact integrated_magnitude_le constant coefficients displacement 0
  | count + 1 => by
      have previous := integrated_partialSum_le constant coefficients displacement count
      have next := integrated_magnitude_le constant coefficients displacement (count + 1)
      rw [partialSum_succ, partialSum_succ (tailMagnitudes coefficients displacement)]
      change le _ (mul (abs (displacement 0)) (add (shellMagnitude coefficients displacement 0)
        (add (partialSum (tailMagnitudes coefficients displacement) count)
          (shellMagnitude coefficients displacement (count + 1)))))
      real_grind

/-- The integrated series converges wherever the derivative series does. -/
public theorem integrated_normal (constant : selection.Carrier)
    {coefficients : MultiIndex.carrier 1 → selection.Carrier}
    {displacement : FiniteVector.carrier 1}
    (normal : NormallyConvergent coefficients displacement) :
    NormallyConvergent (integratedCoefficients constant coefficients) displacement := by
  obtain ⟨upper, bound⟩ := normal
  refine ⟨mul (abs (displacement 0)) (add (shellMagnitude coefficients displacement 0) upper),
    fun count => ?_⟩
  have growing : le (partialSum (tailMagnitudes (integratedCoefficients constant coefficients)
      displacement) count) (partialSum (tailMagnitudes (integratedCoefficients constant
        coefficients) displacement) (count + 1)) := by
    rw [partialSum_succ]
    have := abs_nonnegative (mul (integratedCoefficients constant coefficients
      (lineIndex (count + 1))) (power (displacement 0) (count + 1)))
    rw [← shellMagnitude_line] at this
    change le zero (tailMagnitudes _ displacement count) at this
    real_grind
  refine le_trans growing (le_trans (integrated_partialSum_le constant coefficients
    displacement count) ?_)
  exact mul_le_mul_nonnegative_left (add_le_add (le_refl _) (bound count))
    (abs_nonnegative _)

/-- The term-by-term integral of a convergent series, on the same ball. -/
@[expose] public def integratedSeries (constant : selection.Carrier) (series : Convergent 1) :
    Convergent 1 where
  coefficients := integratedCoefficients constant series.coefficients
  radius := series.radius
  radiusPositive := series.radiusPositive
  normalOn := fun displacement inside =>
    integrated_normal constant (series.normalOn displacement inside)

/-- Differentiating the integrated coefficients recovers the original ones. -/
public theorem integrated_derivative_coefficients (constant : selection.Carrier)
    (series : Convergent 1) :
    (partialDerivativeSeries (integratedSeries constant series) 0).coefficients =
      series.coefficients := by
  funext index
  change mul (naturalScale (index 0 + 1))
    (integratedCoefficients constant series.coefficients
      (MultiIndex.addIndex index (MultiIndex.unitIndex 0))) = _
  change mul (naturalScale (index 0 + 1))
    (div (series.coefficients (lineIndex (index 0))) (naturalScale (index 0 + 1))) = _
  rw [← line_index_eq index]
  have scaleNonzero := nonzero_of_positive (naturalScale_succ_positive (index 0))
  rw [div_eq_mul_inverse]
  real_grind

private theorem value_of_coefficients {first second : Convergent 1}
    (same : first.coefficients = second.coefficients)
    {firstDisplacement secondDisplacement : FiniteVector.carrier 1}
    (equal : firstDisplacement = secondDisplacement)
    (firstInside : FiniteVector.ball (FiniteVector.zeroVector 1) first.radius firstDisplacement)
    (secondInside :
      FiniteVector.ball (FiniteVector.zeroVector 1) second.radius secondDisplacement) :
    value first firstDisplacement firstInside = value second secondDisplacement secondInside := by
  subst equal
  obtain ⟨firstCoefficients, _, _, _⟩ := first
  obtain ⟨secondCoefficients, _, _, _⟩ := second
  change firstCoefficients = secondCoefficients at same
  subst same
  rfl

private theorem replace_line (value argument : selection.Carrier) :
    replaceCoordinate (linePoint value) 0 argument = linePoint argument := by
  funext coordinate
  rw [fin_one_eq_zero coordinate]
  rfl

private theorem hasDerivative_of_translate {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier}
    (translated : HasDerivative (fun step => function (add point step)) zero derivative) :
    HasDerivative function point derivative := by
  refine approaches_congr_near one_positive (fun step _ _ => ?_) translated
  simp only [secant, zero_add, add_zero]

/-- A function of one coordinate whose derivative is analytic on an open region
is analytic there. -/
public theorem analytic_on_of_hasDerivative {region : FiniteVector.carrier 1 → Prop}
    {antiderivative derivative : selection.Carrier → selection.Carrier}
    (analytic : AnalyticOn region (fun point => derivative (point 0)))
    (differentiable : ∀ point, region point →
      HasDerivative antiderivative (point 0) (derivative (point 0))) :
    AnalyticOn region (fun point => antiderivative (point 0)) := by
  refine ⟨analytic.left, fun center member => ?_⟩
  obtain ⟨series, included, agree⟩ := analytic.right center member
  let origin := center 0
  let integral := integratedSeries (antiderivative origin) series
  let derivativeSeries := partialDerivativeSeries integral 0
  let radius := derivativeSeries.radius
  have radiusBelow : le radius series.radius := partialDerivativeSeries_radius_le integral 0
  let curve := fun step => totalValue integral (linePoint step)
  -- The integrated series differentiates to the derivative on the smaller ball.
  have curveDerivative : ∀ step, lt (abs step) radius →
      HasDerivative curve step (derivative (add origin step)) := by
    intro step small
    have stepInside : FiniteVector.ball (FiniteVector.zeroVector 1) radius (linePoint step) := by
      intro coordinate
      change lt (abs (sub step zero)) radius
      rwa [sub_zero]
    have pointInside : FiniteVector.ball center series.radius (linePoint (add origin step)) := by
      intro coordinate
      rw [fin_one_eq_zero coordinate]
      change lt (abs (sub (add origin step) origin)) series.radius
      rw [add_sub_self]
      exact lt_of_lt_of_le small radiusBelow
    have seriesDerivative := coordinateValueAround_has_derivative_partial_series integral
      (linePoint step) 0 stepInside
    have gapPositive : lt zero (sub series.radius (abs step)) :=
      sub_positive_iff.mpr (lt_of_lt_of_le small radiusBelow)
    have near : NearZero fun shift =>
        coordinateValueAround integral (linePoint step) 0 shift = curve (add step shift) := by
      refine ⟨sub series.radius (abs step), gapPositive, fun shift close => ?_⟩
      show coordinateValueAround integral (linePoint step) 0 shift = curve (add step shift)
      have shiftedInside : FiniteVector.ball (FiniteVector.zeroVector 1) integral.radius
          (linePoint (add step shift)) := by
        intro coordinate
        change lt (abs (sub (add step shift) zero)) series.radius
        rw [sub_zero]
        have triangle := abs_add_le step shift
        real_grind
      have replaced : FiniteVector.ball (FiniteVector.zeroVector 1) integral.radius
          (replaceCoordinate (linePoint step) 0 (add (linePoint step 0) shift)) := by
        rw [replace_line]
        exact shiftedInside
      rw [coordinateValueAround_of_inside integral (linePoint step) 0 shift replaced]
      change _ = totalValue integral (linePoint (add step shift))
      rw [totalValue_of_inside integral _ shiftedInside]
      congr 1
      exact replace_line step _
    have translated := HasDerivative.congr_near_zero near seriesDerivative
    have sameValue : value derivativeSeries (linePoint step) stepInside =
        derivative (add origin step) := by
      have fromSeries := agree (linePoint (add origin step)) pointInside
      change derivative (add origin step) = _ at fromSeries
      rw [fromSeries]
      refine value_of_coefficients (integrated_derivative_coefficients _ series) ?_ _ _
      funext coordinate
      rw [fin_one_eq_zero coordinate]
      change step = sub (add origin step) origin
      rw [add_sub_self]
    rw [sameValue] at translated
    exact hasDerivative_of_translate translated
  -- The function and the integrated series agree on the smaller ball.
  have equal : ∀ step, lt (abs step) radius →
      antiderivative (add origin step) = curve step := by
    intro step small
    have flat : ∀ point, lt (neg radius) point → lt point radius →
        HasDerivative (fun value => sub (antiderivative (add origin value)) (curve value))
          point zero := by
      intro point lower upper
      have pointSmall : lt (abs point) radius := abs_lt.mpr ⟨lower, upper⟩
      have shifted := hasDerivative_add (hasDerivative_const origin point)
        (hasDerivative_identity point)
      have pointMember : region (linePoint (add origin point)) := by
        apply included
        intro coordinate
        rw [fin_one_eq_zero coordinate]
        change lt (abs (sub (add origin point) origin)) series.radius
        rw [add_sub_self]
        exact lt_of_lt_of_le pointSmall radiusBelow
      have outer := hasDerivative_comp (inner := fun value => add origin value)
        (differentiable _ pointMember) shifted
      have difference := hasDerivative_sub outer (curveDerivative point pointSmall)
      change HasDerivative _ point (sub (mul (derivative (add origin point)) (add zero one))
        (derivative (add origin point))) at difference
      have vanishes : sub (mul (derivative (add origin point)) (add zero one))
          (derivative (add origin point)) = zero := by
        rw [zero_add, mul_one, sub_self]
      rw [vanishes] at difference
      exact difference
    have bounds := abs_lt.mp small
    have radiusPositive := derivativeSeries.radiusPositive
    have same := eq_of_hasDerivative_zero_on flat bounds.1 bounds.2
      (show lt (neg radius) zero by real_grind) radiusPositive
    have atCenter : curve zero = antiderivative origin := by
      have originInside : FiniteVector.ball (FiniteVector.zeroVector 1) integral.radius
          (FiniteVector.zeroVector 1) := by
        intro coordinate
        change lt (abs (sub zero zero)) series.radius
        rw [sub_self, abs_zero]
        exact series.radiusPositive
      change totalValue integral (FiniteVector.zeroVector 1) = _
      rw [totalValue_of_inside integral _ originInside, value_at_origin]
      rfl
    have zeroValue : sub (antiderivative (add origin zero)) (curve zero) = zero := by
      rw [add_zero, atCenter, sub_self]
    change sub (antiderivative (add origin step)) (curve step) =
      sub (antiderivative (add origin zero)) (curve zero) at same
    rw [zeroValue] at same
    real_grind
  refine ⟨restrictRadius integral radius derivativeSeries.radiusPositive radiusBelow,
    fun point inside => included point (FiniteVector.ball_mono radiusBelow inside), ?_⟩
  intro point inside
  have displaced : FiniteVector.subVector point center =
      linePoint (sub (point 0) origin) := by
    funext coordinate
    rw [fin_one_eq_zero coordinate]
    rfl
  have small : lt (abs (sub (point 0) origin)) radius := inside 0
  have recentered := equal (sub (point 0) origin) small
  rw [add_sub_cancel] at recentered
  show antiderivative (point 0) = _
  rw [recentered]
  have valueInside : FiniteVector.ball (FiniteVector.zeroVector 1) integral.radius
      (linePoint (sub (point 0) origin)) := by
    intro coordinate
    change lt (abs (sub (sub (point 0) origin) zero)) series.radius
    rw [sub_zero]
    exact lt_of_lt_of_le small radiusBelow
  change totalValue integral (linePoint (sub (point 0) origin)) = _
  rw [totalValue_of_inside integral _ valueInside]
  apply value_of_coefficients rfl displaced.symm
  rw [displaced]
  exact valueInside

end

end Problib.Analysis.Real.PowerSeries
