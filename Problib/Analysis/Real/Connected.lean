module

public import Problib.Analysis.Real.Limit

/-! Open intervals of the sealed real carrier are connected.

A predicate that is open inside an open interval and closed relative to it
either holds nowhere or everywhere on the interval. The upward half takes the
least upper bound of the points reached from a member without leaving the
predicate. Reflection through negation gives the downward half. The identity
theorem for analytic functions of one variable reads this as its only
topological input.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

/-- Every member of the predicate has an interval neighborhood inside it. -/
@[expose] public def IntervalOpen (lower upper : selection.Carrier)
    (set : selection.Carrier → Prop) : Prop :=
  ∀ point, set point →
    ∃ radius, lt zero radius ∧
      ∀ other, lt (abs (sub other point)) radius →
        lt lower other → lt other upper → set other

/-- Every interval point approximated by members of the predicate is a member. -/
@[expose] public def IntervalClosed (lower upper : selection.Carrier)
    (set : selection.Carrier → Prop) : Prop :=
  ∀ point, lt lower point → lt point upper →
    (∀ radius, lt zero radius →
      ∃ other, set other ∧ lt (abs (sub other point)) radius) →
    set point

private theorem abs_sub_lt_of_above {value center step radius : selection.Carrier}
    (lower : le center value) (upper : le value (add center step))
    (small : lt step radius) :
    lt (abs (sub value center)) radius := by
  have nonnegative : le zero (sub value center) := by
    have shifted := add_le_add_right_iff (shift := neg center) |>.mpr lower
    rwa [add_neg, ← sub_eq_add_neg] at shifted
  rw [abs_of_nonnegative nonnegative]
  have shifted := add_le_add_right_iff (shift := neg center) |>.mpr upper
  rw [← sub_eq_add_neg, ← sub_eq_add_neg, add_sub_self] at shifted
  exact lt_of_le_of_lt shifted small

private theorem abs_sub_lt_of_below {value center step radius : selection.Carrier}
    (lower : le (sub center step) value) (upper : le value center)
    (small : lt step radius) :
    lt (abs (sub value center)) radius := by
  rw [abs_sub_comm]
  apply abs_sub_lt_of_above upper _ small
  have shifted := add_le_add_right_iff (shift := step) |>.mpr lower
  rwa [sub_add_cancel] at shifted

private theorem le_of_not_lt {left right : selection.Carrier}
    (failure : ¬lt left right) : le right left := by
  classical
  rcases le_total right left with ordered | reversed
  · exact ordered
  · exact Classical.byContradiction fun missing => failure ⟨reversed, missing⟩

private theorem sub_half_lt {value radius : selection.Carrier}
    (positive : lt zero radius) : lt (sub value (half radius)) value := by
  apply sub_positive_iff.mp
  rw [sub_sub_cancel]
  exact half_positive positive

private theorem lt_add_half {value radius : selection.Carrier}
    (positive : lt zero radius) : lt value (add value (half radius)) := by
  simpa only [add_zero] using add_lt_add_left value (half_positive positive)

private theorem half_lt {radius : selection.Carrier}
    (positive : lt zero radius) : lt (half radius) radius := by
  have doubled := add_lt_add_left (half radius) (half_positive positive)
  rwa [add_zero, add_half] at doubled

/-- Upward connectedness: a member reaches every interval point above it. -/
public theorem interval_connected_up {lower upper : selection.Carrier}
    {set : selection.Carrier → Prop}
    (openSet : IntervalOpen lower upper set)
    (closedSet : IntervalClosed lower upper set)
    {start target : selection.Carrier}
    (startMember : set start) (lowerStart : lt lower start)
    (targetUpper : lt target upper) (ordered : le start target) :
    set target := by
  classical
  let reached : selection.Carrier → Prop := fun value =>
    le start value ∧ le value target ∧
      ∀ other, le start other → le other value → set other
  have startReached : reached start := by
    refine ⟨le_refl start, ordered, fun other above below => ?_⟩
    rw [le_antisymm below above]
    exact startMember
  rcases exists_lub reached ⟨start, startReached⟩
    ⟨target, fun value member => member.2.1⟩ with
    ⟨least, leastUpper, leastBelow⟩
  have startLeast : le start least := leastUpper start startReached
  have leastTarget : le least target :=
    leastBelow target (fun value member => member.2.1)
  have below : ∀ other, le start other → lt other least → set other := by
    intro other above less
    have notUpper : ¬Problib.Real.IsUpperBound le reached other :=
      fun bound => not_le_of_lt less (leastBelow other bound)
    unfold Problib.Real.IsUpperBound at notUpper
    rcases Classical.not_forall.mp notUpper with ⟨witness, failure⟩
    rcases Classical.not_imp.mp failure with ⟨witnessReached, notBelow⟩
    exact witnessReached.2.2 other above (le_of_lt (lt_of_not_le notBelow))
  have lowerLeast : lt lower least := lt_of_lt_of_le lowerStart startLeast
  have leastUpperBound : lt least upper := lt_of_le_of_lt leastTarget targetUpper
  have leastMember : set least := by
    apply closedSet least lowerLeast leastUpperBound
    intro radius radiusPositive
    by_cases equal : start = least
    · refine ⟨start, startMember, ?_⟩
      rw [equal, sub_self, abs_zero]
      exact radiusPositive
    · have startBelow : lt start least :=
        ⟨startLeast, fun reverse => equal (le_antisymm startLeast reverse)⟩
      by_cases inside : le start (sub least (half radius))
      · refine ⟨sub least (half radius),
          below _ inside (sub_half_lt radiusPositive), ?_⟩
        exact abs_sub_lt_of_below (step := half radius) (le_refl _)
          (le_of_lt (sub_half_lt radiusPositive)) (half_lt radiusPositive)
      · refine ⟨start, startMember, ?_⟩
        exact abs_sub_lt_of_below (step := half radius)
          (le_of_lt (lt_of_not_le inside)) startLeast (half_lt radiusPositive)
  rcases openSet least leastMember with ⟨radius, radiusPositive, near⟩
  have within : ∀ other, le start other →
      le other (add least (half radius)) → lt other upper → set other := by
    intro other above bound otherUpper
    by_cases less : lt other least
    · exact below other above less
    · have leastOther : le least other := le_of_not_lt less
      exact near other
        (abs_sub_lt_of_above leastOther bound (half_lt radiusPositive))
        (lt_of_lt_of_le lowerStart above) otherUpper
  by_cases reach : le target (add least (half radius))
  · exact within target ordered reach targetUpper
  · have beyond := lt_of_not_le reach
    have stepReached : reached (add least (half radius)) := by
      refine ⟨le_trans startLeast (le_of_lt (lt_add_half radiusPositive)),
        le_of_lt beyond, fun other above bound => ?_⟩
      exact within other above bound
        (lt_of_le_of_lt bound (lt_trans beyond targetUpper))
    exact False.elim (not_le_of_lt (lt_add_half radiusPositive)
      (leastUpper _ stepReached))

private theorem abs_sub_neg (left right : selection.Carrier) :
    abs (sub (neg left) (neg right)) = abs (sub left right) := by
  rw [← neg_sub_distrib, abs_neg]

private theorem reflect_open {lower upper : selection.Carrier}
    {set : selection.Carrier → Prop}
    (openSet : IntervalOpen lower upper set) :
    IntervalOpen (neg upper) (neg lower) (fun value => set (neg value)) := by
  intro point member
  rcases openSet (neg point) member with ⟨radius, positive, near⟩
  refine ⟨radius, positive, fun other close lowerOther otherUpper => ?_⟩
  apply near (neg other)
  · rw [abs_sub_neg]
    exact close
  · have reflected := neg_lt_neg_iff.mpr otherUpper
    rwa [neg_neg] at reflected
  · have reflected := neg_lt_neg_iff.mpr lowerOther
    rwa [neg_neg] at reflected

private theorem reflect_closed {lower upper : selection.Carrier}
    {set : selection.Carrier → Prop}
    (closedSet : IntervalClosed lower upper set) :
    IntervalClosed (neg upper) (neg lower) (fun value => set (neg value)) := by
  intro point lowerPoint pointUpper approximated
  apply closedSet (neg point)
  · have reflected := neg_lt_neg_iff.mpr pointUpper
    rwa [neg_neg] at reflected
  · have reflected := neg_lt_neg_iff.mpr lowerPoint
    rwa [neg_neg] at reflected
  · intro radius positive
    rcases approximated radius positive with ⟨other, member, close⟩
    refine ⟨neg other, member, ?_⟩
    rw [abs_sub_neg]
    exact close

/-- An open, relatively closed predicate with one interval member holds on
the whole open interval. -/
public theorem interval_connected {lower upper : selection.Carrier}
    {set : selection.Carrier → Prop}
    (openSet : IntervalOpen lower upper set)
    (closedSet : IntervalClosed lower upper set)
    {start : selection.Carrier} (startMember : set start)
    (lowerStart : lt lower start) (startUpper : lt start upper)
    {target : selection.Carrier}
    (lowerTarget : lt lower target) (targetUpper : lt target upper) :
    set target := by
  rcases le_total start target with ordered | reversed
  · exact interval_connected_up openSet closedSet startMember lowerStart
      targetUpper ordered
  · have reflected := interval_connected_up (reflect_open openSet)
      (reflect_closed closedSet) (start := neg start) (target := neg target)
      (by simpa only [neg_neg] using startMember)
      (neg_lt_neg_iff.mpr startUpper) (neg_lt_neg_iff.mpr lowerTarget)
      (neg_le_neg_iff.mpr reversed)
    simpa only [neg_neg] using reflected

end

end Problib.Analysis.Real
