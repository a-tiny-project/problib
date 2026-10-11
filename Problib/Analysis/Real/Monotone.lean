module

public import Problib.Analysis.Real.MeanValue
public import Problib.Analysis.Real.Calculus
public import Problib.Real.Grind

/-! A function with a nonnegative derivative on an open interval increases there.

The argument is `MeanValue`'s with a one-sided bound. Fix a start inside the
interval and a positive slope. The points up to which the function stays above
its start value less the slope times the distance form a set that a
nonnegative derivative extends forward and continuity closes. Interval
connectedness carries the set to every later point. Every slope works, so the
function does not decrease.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

private theorem le_of_not_lt' {left right : selection.Carrier}
    (notLess : ¬lt left right) : le right left := by
  classical
  rcases le_total right left with ordered | reverse
  · exact ordered
  · exact Classical.byContradiction fun notOrdered => notLess ⟨reverse, notOrdered⟩

/-- The points up to which the function stays above its value at `start`, less
`slope` times the distance. -/
private def Above (function : selection.Carrier → selection.Carrier)
    (start slope : selection.Carrier) : selection.Carrier → Prop :=
  fun point => ∀ other, le start other → le other point →
    le (sub (function start) (mul slope (sub other start))) (function other)

private theorem above_open {function derivative : selection.Carrier → selection.Carrier}
    {lower upper : selection.Carrier}
    (differentiable : ∀ point, lt lower point → lt point upper →
      HasDerivative function point (derivative point))
    (nonnegative : ∀ point, lt lower point → lt point upper → le zero (derivative point))
    {start slope : selection.Carrier} (positive : lt zero slope) (lowerStart : lt lower start) :
    IntervalOpen lower upper (Above function start slope) := by
  intro point member
  classical
  by_cases beyond : le upper point
  · refine ⟨one, one_positive, fun other _ _ otherUpper => ?_⟩
    intro middle startMiddle middleOther
    exact member middle startMiddle
      (le_trans middleOther (le_trans (le_of_lt otherUpper) beyond))
  by_cases before : lt point start
  · refine ⟨sub start point, sub_positive_iff.mpr before, fun other close _ _ => ?_⟩
    intro middle startMiddle middleOther
    have below : lt other start := by
      have bounded := lt_of_le_of_lt (le_abs _) close
      real_grind
    exact False.elim (not_le_of_lt below (le_trans startMiddle middleOther))
  · have startPoint : le start point := le_of_not_lt' before
    have pointUpper : lt point upper := lt_of_not_le beyond
    have lowerPoint : lt lower point := lt_of_lt_of_le lowerStart startPoint
    rcases differentiable point lowerPoint pointUpper slope positive with
      ⟨radius, radiusPositive, close⟩
    refine ⟨radius, radiusPositive, fun other near _ _ => ?_⟩
    intro middle startMiddle middleOther
    by_cases early : le middle point
    · exact member middle startMiddle early
    · have pointMiddle : lt point middle := lt_of_not_le early
      have stepPositive : lt zero (sub middle point) := sub_positive_iff.mpr pointMiddle
      have stepNonzero : sub middle point ≠ zero := nonzero_of_positive stepPositive
      have stepSmall : lt (abs (sub middle point)) radius := by
        rw [abs_of_nonnegative (le_of_lt stepPositive)]
        have bounded := lt_of_le_of_lt (le_abs _) near
        real_grind
      have secantClose := (abs_lt.mp (close (sub middle point) stepNonzero stepSmall)).1
      have derivativeNonnegative := nonnegative point lowerPoint pointUpper
      have secantAbove : lt (neg slope) (secant function point (sub middle point)) := by
        real_grind
      have scaled := mul_lt_mul_positive_right secantAbove stepPositive
      unfold secant at scaled
      rw [div_mul_cancel _ stepNonzero, add_sub_cancel] at scaled
      have previous := member point startPoint (le_refl point)
      have scaledLe := le_of_lt scaled
      real_grind

private theorem above_closed {function derivative : selection.Carrier → selection.Carrier}
    {lower upper : selection.Carrier}
    (differentiable : ∀ point, lt lower point → lt point upper →
      HasDerivative function point (derivative point))
    {start slope : selection.Carrier} (positive : lt zero slope) :
    IntervalClosed lower upper (Above function start slope) := by
  intro point lowerPoint pointUpper approximated middle startMiddle middlePoint
  classical
  by_cases strictly : lt middle point
  · rcases approximated (sub point middle) (sub_positive_iff.mpr strictly) with
      ⟨other, member, close⟩
    have otherAbove : le middle other := by
      have bounded := neg_abs_le (sub other point)
      apply le_of_not_lt'
      intro otherBelow
      real_grind
    exact member middle startMiddle otherAbove
  · have same : middle = point := le_antisymm middlePoint (le_of_not_lt' strictly)
    subst same
    apply le_of_le_add_positive
    intro error errorPositive
    rcases hasDerivative_continuous (differentiable middle lowerPoint pointUpper) error
      errorPositive with ⟨radius, radiusPositive, near⟩
    have closeValue : ∀ other, lt (abs (sub other middle)) radius →
        le (function other) (add (function middle) error) := by
      intro other close
      by_cases equal : sub other middle = zero
      · have otherPoint : other = middle := by
          rw [← add_sub_cancel other middle, equal, add_zero]
        rw [otherPoint]
        have := le_of_lt errorPositive
        real_grind
      · have value := (abs_lt.mp (near (sub other middle) equal close)).2
        simp only [] at value
        rw [add_sub_cancel] at value
        have := le_of_lt value
        real_grind
    have slopeNonnegative : le zero (mul slope (sub middle start)) :=
      mul_nonnegative (le_of_lt positive) (sub_nonnegative startMiddle)
    rcases approximated radius radiusPositive with ⟨other, member, close⟩
    by_cases startOther : le start other
    · by_cases otherPoint : le other middle
      · have bound := member other startOther (le_refl other)
        have raised : le (mul slope (sub other start)) (mul slope (sub middle start)) := by
          apply mul_le_mul_nonnegative_left _ (le_of_lt positive)
          real_grind
        have closer := closeValue other close
        real_grind
      · have bound := member middle startMiddle (le_of_not_lt' fun less => otherPoint
          (le_of_lt less))
        have := le_of_lt errorPositive
        real_grind
    · have otherStart : lt other start := lt_of_not_le startOther
      have startClose : lt (abs (sub start middle)) radius := by
        rw [abs_of_nonpositive (by real_grind)]
        have bounded := neg_abs_le (sub other middle)
        real_grind
      have bound := closeValue start startClose
      real_grind

private theorem above_start (function : selection.Carrier → selection.Carrier)
    (start slope : selection.Carrier) : Above function start slope start := by
  intro other startOther otherStart
  rw [le_antisymm otherStart startOther, sub_self, mul_zero, sub_zero]
  exact le_refl _

/-- A function whose derivative is nonnegative at every point of an open
interval does not decrease across it. -/
public theorem le_of_hasDerivative_nonnegative
    {function derivative : selection.Carrier → selection.Carrier}
    {lower upper : selection.Carrier}
    (differentiable : ∀ point, lt lower point → lt point upper →
      HasDerivative function point (derivative point))
    (nonnegative : ∀ point, lt lower point → lt point upper → le zero (derivative point))
    {first second : selection.Carrier} (lowerFirst : lt lower first)
    (secondUpper : lt second upper) (ordered : le first second) :
    le (function first) (function second) := by
  have distanceNonnegative : le zero (sub second first) := sub_nonnegative ordered
  apply le_of_le_add_positive
  intro error errorPositive
  have gapPositive : lt zero (add (sub second first) one) := by
    have := one_positive
    real_grind
  let slope := div error (add (sub second first) one)
  have slopePositive : lt zero slope :=
    mul_positive errorPositive (inverse_of_positive_positive gapPositive)
  have reached := interval_connected_up
    (above_open differentiable nonnegative slopePositive lowerFirst)
    (above_closed differentiable slopePositive) (above_start function first slope)
    lowerFirst secondUpper ordered
  have bound := reached second ordered (le_refl second)
  have raised : le (mul slope (sub second first)) (mul slope (add (sub second first) one)) := by
    apply mul_le_mul_nonnegative_left _ (le_of_lt slopePositive)
    have := one_positive
    real_grind
  rw [show mul slope (add (sub second first) one) = error from by
    rw [mul_comm]; exact (mul_comm _ _).trans (div_mul_cancel _ (nonzero_of_positive gapPositive))]
    at raised
  real_grind

/-- A function whose derivative is nonpositive at every point of an open
interval does not increase across it. -/
public theorem le_of_hasDerivative_nonpositive
    {function derivative : selection.Carrier → selection.Carrier}
    {lower upper : selection.Carrier}
    (differentiable : ∀ point, lt lower point → lt point upper →
      HasDerivative function point (derivative point))
    (nonpositive : ∀ point, lt lower point → lt point upper → le (derivative point) zero)
    {first second : selection.Carrier} (lowerFirst : lt lower first)
    (secondUpper : lt second upper) (ordered : le first second) :
    le (function second) (function first) := by
  have negated := le_of_hasDerivative_nonnegative (function := fun point => neg (function point))
    (derivative := fun point => neg (derivative point))
    (fun point lowerPoint pointUpper =>
      hasDerivative_neg (differentiable point lowerPoint pointUpper))
    (fun point lowerPoint pointUpper => by
      have := nonpositive point lowerPoint pointUpper
      real_grind)
    lowerFirst secondUpper ordered
  real_grind

end

end Problib.Analysis.Real
