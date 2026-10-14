module

public import Problib.Analysis.Real.Connected
public import Problib.Analysis.Real.Derivative

/-! A function with zero derivative on an open interval is constant there.

Fix a start inside the interval and a positive slope. The points up to which
the function has moved from its start value by at most the slope times the
distance form a set that a zero derivative extends forward and continuity
closes. By interval connectedness the set reaches every later point of the
interval. Every slope works, so the function does not move. A zero derivative
everywhere is the case of an interval around any two points.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

private theorem abs_sub_triangle (first middle last : selection.Carrier) :
    le (abs (sub first last))
      (add (abs (sub first middle)) (abs (sub middle last))) := by
  rw [← sub_add_sub first middle last]
  exact abs_add_le _ _

private theorem le_of_not_lt' {left right : selection.Carrier}
    (notLess : ¬lt left right) : le right left := by
  classical
  rcases le_total right left with ordered | reverse
  · exact ordered
  · exact Classical.byContradiction fun notOrdered => notLess ⟨reverse, notOrdered⟩

private theorem sub_le_sub_of_le {left right : selection.Carrier}
    (included : le left right) (shift : selection.Carrier) :
    le (sub left shift) (sub right shift) := by
  have shifted := add_le_add included (le_refl (neg shift))
  rwa [← sub_eq_add_neg, ← sub_eq_add_neg] at shifted

private theorem sub_le_sub_left_of_le {left right : selection.Carrier}
    (included : le left right) (value : selection.Carrier) :
    le (sub value right) (sub value left) := by
  apply (add_le_add_right_iff (shift := add left right)).mp
  have leftSide : add (sub value right) (add left right) = add value left := by
    rw [add_comm left right, ← add_assoc, sub_add_cancel]
  have rightSide : add (sub value left) (add left right) = add value right := by
    rw [← add_assoc, sub_add_cancel]
  rw [leftSide, rightSide]
  exact add_le_add (le_refl value) included

/-- A value within every positive slack of a bound is at most the bound. -/
public theorem le_of_le_add_positive {value bound : selection.Carrier}
    (slack : ∀ error, lt zero error → le value (add bound error)) :
    le value bound := by
  classical
  by_cases below : le value bound
  · exact below
  · have above : lt bound value := ⟨le_of_not_lt' (fun less => below less.1), below⟩
    have gapPositive : lt zero (sub value bound) := sub_positive_iff.mpr above
    have halfBelow : lt (half (sub value bound)) (sub value bound) := by
      have doubled := add_lt_add_left (half (sub value bound)) (half_positive gapPositive)
      rwa [add_zero, add_half] at doubled
    have shifted := add_lt_add_left bound halfBelow
    rw [add_sub_cancel] at shifted
    exact False.elim (lt_irrefl value
      (lt_of_le_of_lt (slack _ (half_positive gapPositive)) shifted))

private theorem increment_small {function : selection.Carrier → selection.Carrier}
    {point : selection.Carrier} (flat : HasDerivative function point zero)
    {slope : selection.Carrier} (positive : lt zero slope) :
    ∃ radius, lt zero radius ∧ ∀ step, lt (abs step) radius →
      le (abs (sub (function (add point step)) (function point)))
        (mul slope (abs step)) := by
  rcases flat slope positive with ⟨radius, radiusPositive, close⟩
  refine ⟨radius, radiusPositive, fun step small => ?_⟩
  classical
  by_cases vanished : step = zero
  · rw [vanished, add_zero, sub_self, abs_zero, mul_zero]
    exact le_refl zero
  · have near := close step vanished small
    rw [sub_zero, secant, abs_div] at near
    have scaled := mul_lt_mul_positive_right near (abs_positive_of_nonzero vanished)
    have absoluteNonzero : abs step ≠ zero := fun absent =>
      vanished (abs_eq_zero_iff.mp absent)
    rw [div_mul_cancel _ absoluteNonzero] at scaled
    exact le_of_lt scaled

/-- The points up to which the function stays within `slope` times the
distance of its value at `start`. -/
private def Within (function : selection.Carrier → selection.Carrier)
    (start slope : selection.Carrier) : selection.Carrier → Prop :=
  fun point => ∀ other, le start other → le other point →
    le (abs (sub (function other) (function start)))
      (mul slope (sub other start))

private theorem within_open {function : selection.Carrier → selection.Carrier}
    {lower upper : selection.Carrier}
    (flat : ∀ point, lt lower point → lt point upper → HasDerivative function point zero)
    {start slope : selection.Carrier} (positive : lt zero slope) (lowerStart : lt lower start) :
    IntervalOpen lower upper (Within function start slope) := by
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
    have shifted := add_lt_add_left point (lt_of_le_of_lt (le_abs _) close)
    rw [add_sub_cancel, add_sub_cancel] at shifted
    exact False.elim (lt_irrefl start
      (lt_of_le_of_lt (le_trans startMiddle middleOther) shifted))
  · have startPoint : le start point := le_of_not_lt' before
    have pointUpper : lt point upper :=
      ⟨(le_total point upper).resolve_right beyond, fun above => beyond above⟩
    rcases increment_small (flat point (lt_of_lt_of_le lowerStart startPoint) pointUpper)
      positive with ⟨radius, radiusPositive, small⟩
    refine ⟨radius, radiusPositive, fun other close _ _ => ?_⟩
    intro middle startMiddle middleOther
    by_cases early : le middle point
    · exact member middle startMiddle early
    · have pointMiddle : le point middle :=
        (le_total point middle).resolve_right early
      have stepNonnegative := sub_nonnegative pointMiddle
      have stepSmall : lt (abs (sub middle point)) radius := by
        rw [abs_of_nonnegative stepNonnegative]
        exact lt_of_le_of_lt (sub_le_sub_of_le middleOther point)
          (lt_of_le_of_lt (le_abs _) close)
      have increment := small (sub middle point) stepSmall
      rw [add_sub_cancel, abs_of_nonnegative stepNonnegative] at increment
      have previous := member point startPoint (le_refl point)
      refine le_trans (abs_sub_triangle _ (function point) _) ?_
      rw [← sub_add_sub middle point start, mul_add]
      exact add_le_add increment previous

private theorem within_closed {function : selection.Carrier → selection.Carrier}
    {lower upper : selection.Carrier}
    (flat : ∀ point, lt lower point → lt point upper → HasDerivative function point zero)
    {start slope : selection.Carrier} (positive : lt zero slope) :
    IntervalClosed lower upper (Within function start slope) := by
  intro point lowerPoint pointUpper approximated middle startMiddle middlePoint
  classical
  by_cases strictly : lt middle point
  · rcases approximated (sub point middle) (sub_positive_iff.mpr strictly) with
      ⟨other, member, close⟩
    have otherAbove : le middle other := by
      apply le_of_not_lt'
      intro otherBelow
      have reversed := sub_le_sub_left_of_le (le_of_lt otherBelow) point
      have far : lt (sub point other) (sub point middle) :=
        lt_of_le_of_lt (le_abs _) (by rwa [abs_sub_comm] at close)
      exact lt_irrefl _ (lt_of_le_of_lt reversed far)
    exact member middle startMiddle otherAbove
  · have same : middle = point :=
      le_antisymm middlePoint (le_of_not_lt' strictly)
    rw [same]
    rw [same] at startMiddle
    apply le_of_le_add_positive
    intro error errorPositive
    rcases hasDerivative_continuous (flat point lowerPoint pointUpper) error errorPositive with
      ⟨radius, radiusPositive, near⟩
    have closeValue : ∀ other, lt (abs (sub other point)) radius →
        le (abs (sub (function point) (function other))) error := by
      intro other close
      by_cases equal : sub other point = zero
      · have otherPoint : other = point := by
          rw [← add_sub_cancel other point, equal, add_zero]
        rw [otherPoint, sub_self, abs_zero]
        exact le_of_lt errorPositive
      · have value : lt (abs (sub (function (add point (sub other point)))
            (function point))) error := near (sub other point) equal close
        rw [add_sub_cancel, abs_sub_comm] at value
        exact le_of_lt value
    have slopeNonnegative : le zero (mul slope (sub point start)) :=
      mul_nonnegative (le_of_lt positive) (sub_nonnegative startMiddle)
    rcases approximated radius radiusPositive with ⟨other, member, close⟩
    by_cases startOther : le start other
    · by_cases otherPoint : le other point
      · have bound := member other startOther (le_refl other)
        have raised : le (mul slope (sub other start)) (mul slope (sub point start)) :=
          mul_le_mul_nonnegative_left (sub_le_sub_of_le otherPoint start)
            (le_of_lt positive)
        refine le_trans (abs_sub_triangle _ (function other) _) ?_
        rw [add_comm (mul slope (sub point start)) error]
        exact add_le_add (closeValue other close) (le_trans bound raised)
      · have bound := member point startMiddle
          ((le_total point other).resolve_right otherPoint)
        refine le_trans bound ?_
        have grown := add_le_add (le_refl (mul slope (sub point start)))
          (le_of_lt errorPositive)
        rwa [add_zero] at grown
    · have otherStart : le other start := (le_total other start).resolve_right startOther
      have startClose : lt (abs (sub start point)) radius := by
        rw [abs_sub_comm, abs_of_nonnegative (sub_nonnegative startMiddle)]
        exact lt_of_le_of_lt (sub_le_sub_left_of_le otherStart point)
          (lt_of_le_of_lt (le_abs _) (by rwa [abs_sub_comm] at close))
      have bound := closeValue start startClose
      have grown := add_le_add slopeNonnegative bound
      rwa [zero_add] at grown

private theorem within_start {function : selection.Carrier → selection.Carrier}
    (start slope : selection.Carrier) : Within function start slope start := by
  intro other startOther otherStart
  rw [le_antisymm otherStart startOther, sub_self, sub_self, abs_zero, mul_zero]
  exact le_refl zero

private theorem lt_add_one (value : selection.Carrier) : lt value (add value one) := by
  have shifted := add_lt_add_left value one_positive
  rwa [add_zero] at shifted

private theorem sub_one_lt (value : selection.Carrier) : lt (sub value one) value := by
  apply sub_positive_iff.mp
  rw [sub_sub_cancel]
  exact one_positive

private theorem constant_forward {function : selection.Carrier → selection.Carrier}
    {lower upper : selection.Carrier}
    (flat : ∀ point, lt lower point → lt point upper → HasDerivative function point zero)
    {first second : selection.Carrier} (lowerFirst : lt lower first)
    (secondUpper : lt second upper) (ordered : le first second) :
    function second = function first := by
  let distance := sub second first
  have distanceNonnegative : le zero distance := sub_nonnegative ordered
  have bounded : ∀ slope, lt zero slope →
      le (abs (sub (function second) (function first))) (mul slope distance) := by
    intro slope positive
    have reached := interval_connected_up (within_open flat positive lowerFirst)
      (within_closed flat positive) (within_start first slope) lowerFirst secondUpper ordered
    exact reached second ordered (le_refl second)
  have vanishes : le (abs (sub (function second) (function first))) zero := by
    apply le_of_le_add_positive
    intro error errorPositive
    rw [zero_add]
    have gapPositive : lt zero (add distance one) :=
      lt_of_le_of_lt distanceNonnegative (lt_add_one distance)
    have gapNonzero : add distance one ≠ zero := fun vanished => by
      rw [vanished] at gapPositive
      exact lt_irrefl zero gapPositive
    let slope := div error (add distance one)
    have slopePositive : lt zero slope :=
      mul_positive errorPositive (inverse_of_positive_positive gapPositive)
    refine le_trans (bounded slope slopePositive) ?_
    have raised := mul_le_mul_nonnegative_left (le_of_lt (lt_add_one distance))
      (le_of_lt slopePositive)
    rwa [div_mul_cancel _ gapNonzero] at raised
  have zeroAbs : abs (sub (function second) (function first)) = zero :=
    le_antisymm vanishes (abs_nonnegative _)
  rw [← add_sub_cancel (function second) (function first),
    abs_eq_zero_iff.mp zeroAbs, add_zero]

/-- A function whose derivative is zero at every point of an open interval
takes one value on it. -/
public theorem eq_of_hasDerivative_zero_on
    {function : selection.Carrier → selection.Carrier} {lower upper : selection.Carrier}
    (flat : ∀ point, lt lower point → lt point upper → HasDerivative function point zero)
    {first second : selection.Carrier} (lowerFirst : lt lower first)
    (firstUpper : lt first upper) (lowerSecond : lt lower second)
    (secondUpper : lt second upper) : function first = function second := by
  rcases le_total first second with ordered | reverse
  · exact (constant_forward flat lowerFirst secondUpper ordered).symm
  · exact constant_forward flat lowerSecond firstUpper reverse

/-- A function whose derivative is zero at every point is constant. -/
public theorem eq_of_hasDerivative_zero
    {function : selection.Carrier → selection.Carrier}
    (flat : ∀ point, HasDerivative function point zero)
    (first second : selection.Carrier) : function first = function second := by
  rcases le_total first second with ordered | reverse
  · exact (constant_forward (fun point _ _ => flat point) (sub_one_lt first)
      (lt_add_one second) ordered).symm
  · exact constant_forward (fun point _ _ => flat point) (sub_one_lt second)
      (lt_add_one first) reverse

end

end Problib.Analysis.Real
