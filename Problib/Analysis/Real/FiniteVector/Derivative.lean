module

public import Problib.Analysis.Real.Increment
public import Problib.Analysis.Real.FiniteVector.Complete
public import Problib.Analysis.Real.FiniteVector.Linear

/-! The derivative of a map between finite vector spaces, and the mean value
inequality.

A map has derivative `L` at a point when `L` approximates its increments there
with an error small against the displacement. This is the total (Fréchet)
derivative in the sup norm. Along a line through the point, each coordinate of
the map then has the ordinary derivative given by `L` applied to the line's
direction. That reduces the several-variable mean value inequality to the
one-variable one: on a ball where the derivative stretches vectors by at most
`bound`, the map moves points of the inner quarter ball by at most `bound`
times their distance. The quarter keeps every segment between such points,
extended a little at both ends, inside the ball, with no convexity argument.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.FiniteVector

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

/-- `derivative` approximates `function` near `point`, with an error small
against the displacement. -/
@[expose] public def HasFrechetDerivative {source target : Nat}
    (function : carrier source → carrier target) (point : carrier source)
    (derivative : BoundedLinear source target) : Prop :=
  ∀ epsilon, lt zero epsilon → ∃ radius, lt zero radius ∧
    ∀ displacement, lt (supNorm displacement) radius →
      le (supNorm (subVector
            (subVector (function (addVector point displacement)) (function point))
            (derivative.map displacement)))
        (mul epsilon (supNorm displacement))

/-- A derivative is determined by its action, not by its bound. -/
public theorem HasFrechetDerivative.congr {source target : Nat}
    {function : carrier source → carrier target} {point : carrier source}
    {first second : BoundedLinear source target}
    (differentiable : HasFrechetDerivative function point first)
    (same : ∀ value, first.map value = second.map value) :
    HasFrechetDerivative function point second := by
  intro epsilon positive
  rcases differentiable epsilon positive with ⟨radius, radiusPositive, close⟩
  exact ⟨radius, radiusPositive, fun displacement small => by
    rw [← same]
    exact close displacement small⟩

/-- On an open region, `function` has a derivative at every point, and the
derivative moves continuously in operator norm. -/
public structure ContinuouslyDifferentiableOn {source target : Nat}
    (region : carrier source → Prop) (function : carrier source → carrier target)
    (derivative : carrier source → BoundedLinear source target) : Prop where
  isOpen : IsOpen region
  differentiable : ∀ point, region point →
    HasFrechetDerivative function point (derivative point)
  continuous : ∀ point, region point → ∀ epsilon, lt zero epsilon →
    ∃ radius, lt zero radius ∧ ∀ nearby, ball point radius nearby → ∀ value,
      le (supNorm (subVector ((derivative nearby).map value)
            ((derivative point).map value)))
        (mul epsilon (supNorm value))

/-- Continuous differentiability transports across derivatives with the same
action at every point. -/
public theorem ContinuouslyDifferentiableOn.congr {source target : Nat}
    {region : carrier source → Prop} {function : carrier source → carrier target}
    {first second : carrier source → BoundedLinear source target}
    (smooth : ContinuouslyDifferentiableOn region function first)
    (same : ∀ point, region point → ∀ value,
      (first point).map value = (second point).map value) :
    ContinuouslyDifferentiableOn region function second where
  isOpen := smooth.isOpen
  differentiable := fun point inside =>
    (smooth.differentiable point inside).congr (same point inside)
  continuous := fun point inside epsilon positive => by
    rcases smooth.continuous point inside epsilon positive with ⟨radius, radiusPositive, close⟩
    rcases smooth.isOpen point inside with ⟨openRadius, openPositive, openBall⟩
    rcases small_positive radiusPositive openPositive with ⟨small, smallPositive, leRadius, leOpen⟩
    refine ⟨small, smallPositive, fun nearby near value => ?_⟩
    rw [← same point inside, ← same nearby (openBall nearby (ball_mono leOpen near))]
    exact close nearby (ball_mono leRadius near) value

private theorem secant_residual {first second slope step : selection.Carrier}
    (nonzero : step ≠ zero) :
    sub (div (sub first second) step) slope =
      div (sub (sub first second) (mul step slope)) step := by
  real_grind

private theorem le_add_one (value : selection.Carrier) : le value (add value one) := by
  have := one_positive
  real_grind

private theorem half_lt_self {value : selection.Carrier} (positive : lt zero value) :
    lt (half value) value := by
  simp only [half, two]
  real_grind

private theorem quotient_le {residual step slope : selection.Carrier}
    (positive : lt zero step) (bounded : le residual (mul slope step)) :
    le (div residual step) slope := by
  have scaled := mul_le_mul_nonnegative_left bounded
    (le_of_lt (inverse_of_positive_positive positive))
  rwa [mul_comm slope, ← mul_assoc, inverse_mul_cancel (nonzero_of_positive positive), one_mul,
    mul_comm] at scaled

/-- Along the line through `base` in `direction`, each coordinate of a map has
the ordinary derivative given by its derivative applied to `direction`. -/
public theorem HasFrechetDerivative.along {source target : Nat}
    {function : carrier source → carrier target} {base direction : carrier source}
    {step : selection.Carrier} {derivative : BoundedLinear source target}
    (differentiable : HasFrechetDerivative function
      (addVector base (scaleVector step direction)) derivative)
    (coordinate : Fin target) :
    HasDerivative
      (fun parameter => function (addVector base (scaleVector parameter direction)) coordinate)
      step (derivative.map direction coordinate) := by
  let point := addVector base (scaleVector step direction)
  let size := add (supNorm direction) one
  have sizePositive : lt zero size := by
    have raised := add_le_add (supNorm_nonnegative direction) (le_refl one)
    rw [zero_add] at raised
    exact lt_of_lt_of_le one_positive raised
  have sizeNonzero := nonzero_of_positive sizePositive
  intro epsilon positive
  let tolerance := div (half epsilon) size
  have tolerancePositive : lt zero tolerance :=
    mul_positive (half_positive positive) (inverse_of_positive_positive sizePositive)
  rcases differentiable tolerance tolerancePositive with ⟨radius, radiusPositive, close⟩
  refine ⟨div radius size,
    mul_positive radiusPositive (inverse_of_positive_positive sizePositive), ?_⟩
  intro displacement nonzero small
  have magnitudePositive := abs_positive_of_nonzero nonzero
  have moved : lt (supNorm (scaleVector displacement direction)) radius := by
    rw [supNorm_scaleVector]
    have raised := mul_lt_mul_positive_right small sizePositive
    rw [div_mul_cancel _ sizeNonzero] at raised
    refine lt_of_le_of_lt ?_ raised
    exact mul_le_mul_nonnegative_left (le_add_one _) (abs_nonnegative _)
  have residual := close _ moved
  have shifted : addVector base (scaleVector (add step displacement) direction) =
      addVector point (scaleVector displacement direction) := by
    funext index
    simp only [point, addVector, scaleVector]
    real_grind
  rw [derivative.homogeneous, supNorm_scaleVector, mul_comm (abs displacement),
    ← mul_assoc] at residual
  have atCoordinate := le_trans
    (coordinate_le_supNorm (subVector (subVector (function (addVector point
      (scaleVector displacement direction))) (function point))
      (scaleVector displacement (derivative.map direction))) coordinate) residual
  simp only [subVector, scaleVector] at atCoordinate
  simp only [secant]
  rw [shifted, secant_residual nonzero, abs_div]
  refine lt_of_le_of_lt (quotient_le magnitudePositive atCoordinate) ?_
  have bound : le (mul tolerance (supNorm direction)) (mul tolerance size) :=
    mul_le_mul_nonnegative_left (le_add_one _) (le_of_lt tolerancePositive)
  have atSize : mul tolerance size = half epsilon := div_mul_cancel _ sizeNonzero
  rw [atSize] at bound
  exact lt_of_le_of_lt bound (half_lt_self positive)

/-- A derivative that stretches vectors by at most `bound` on a ball moves
points of the inner quarter ball by at most `bound` times their distance. -/
public theorem supNorm_sub_le_of_derivative_bound {source target : Nat}
    {function : carrier source → carrier target}
    {derivative : carrier source → BoundedLinear source target}
    {center : carrier source} {radius bound : selection.Carrier}
    (positive : lt zero radius) (boundNonnegative : le zero bound)
    (differentiable : ∀ point, ball center radius point →
      HasFrechetDerivative function point (derivative point))
    (bounded : ∀ point, ball center radius point → ∀ value,
      le (supNorm ((derivative point).map value)) (mul bound (supNorm value)))
    {first second : carrier source}
    (firstInside : closedBall center (half (half radius)) first)
    (secondInside : closedBall center (half (half radius)) second) :
    le (supNorm (subVector (function second) (function first)))
      (mul bound (supNorm (subVector second first))) := by
  let direction := subVector second first
  let path := fun parameter => addVector first (scaleVector parameter direction)
  let quarter := half (half radius)
  have quarterPositive : lt zero quarter := half_positive (half_positive positive)
  have directionShort : le (supNorm direction) (add quarter quarter) := by
    refine le_trans (supNorm_sub_triangle second center first) ?_
    rw [supNorm_sub_comm center]
    exact add_le_add secondInside firstInside
  have inside : ∀ parameter, lt (neg (half one)) parameter →
      lt parameter (add one (half one)) → ball center radius (path parameter) := by
    intro parameter above below
    apply (ball_iff_supNorm positive).mpr
    have split : subVector (path parameter) center =
        addVector (subVector first center) (scaleVector parameter direction) := by
      funext index
      simp only [path, addVector, subVector, scaleVector]
      real_grind
    rw [split]
    refine lt_of_le_of_lt (supNorm_triangle _ _) ?_
    rw [supNorm_scaleVector]
    have magnitude : lt (abs parameter) (add one (half one)) := by
      apply abs_lt.mpr
      simp only [half, two] at above below ⊢
      constructor <;> real_grind
    have stretched := mul_le_mul_nonnegative_left directionShort (abs_nonnegative parameter)
    have widened := mul_lt_mul_positive_right magnitude
      (show lt zero (add quarter quarter) from add_positive quarterPositive quarterPositive)
    have whole : add quarter (mul (add one (half one)) (add quarter quarter)) = radius := by
      simp only [quarter, half, two]
      real_grind
    rw [← whole]
    exact lt_of_le_of_lt (add_le_add firstInside stretched) (add_lt_add_left quarter widened)
  have halfPositive := half_positive one_positive
  have zeroAbove : lt (neg (half one)) zero := by real_grind
  have zeroBelow : lt zero (add one (half one)) := by
    have := one_positive
    real_grind
  have oneAbove : lt (neg (half one)) one := by
    have := one_positive
    real_grind
  have oneBelow : lt one (add one (half one)) := by real_grind
  apply supNorm_le (mul_nonnegative boundNonnegative (supNorm_nonnegative _))
  intro coordinate
  have increment := abs_sub_le_of_hasDerivative_bound
    (function := fun parameter => function (path parameter) coordinate)
    (derivative := fun parameter => (derivative (path parameter)).map direction coordinate)
    (bound := mul bound (supNorm direction))
    (fun parameter above below =>
      (differentiable _ (inside parameter above below)).along coordinate)
    (fun parameter above below => le_trans (coordinate_le_supNorm _ coordinate)
      (bounded _ (inside parameter above below) direction))
    zeroAbove zeroBelow oneAbove oneBelow
  have atZero : path zero = first := by
    funext index
    simp only [path, addVector, scaleVector]
    real_grind
  have atOne : path one = second := by
    funext index
    simp only [path, direction, addVector, subVector, scaleVector]
    real_grind
  have unitStep : abs (sub one zero) = one := by
    rw [sub_zero]
    exact abs_of_nonnegative (le_of_lt one_positive)
  simp only [atZero, atOne, unitStep, mul_one] at increment
  exact increment

end

end Problib.Analysis.Real.FiniteVector
