module

public import Problib.Measure.Set.Family
public import Problib.Real.Approximation
public import Problib.Real.Arithmetic

set_option autoImplicit false

namespace Problib.Measure.Real.Compact

open Problib.Real.Construction

local notation "Carrier" => Dedekind.selection.Carrier

/-- The open interval determined by an endpoint pair. -/
@[expose] public def openInterval
    (endpoints : Carrier × Carrier) : Set Carrier :=
  fun value =>
    Dedekind.lt endpoints.1 value ∧
      Dedekind.lt value endpoints.2

/-- The closed interval from `left` to `right`. -/
@[expose] public def closedInterval
    (left right : Carrier) : Set Carrier :=
  fun value => Dedekind.le left value ∧ Dedekind.le value right

/-- Enlarging a prefix preserves every point already covered. -/
public theorem prefix_cover_monotone
    (intervals : Nat → Carrier × Carrier)
    {first second : Nat} (included : first ≤ second) :
    Set.Subset
      (Set.prefixUnion (fun index => openInterval (intervals index)) first)
      (Set.prefixUnion (fun index => openInterval (intervals index)) second) :=
  Set.prefixUnion_monotone _ included

private theorem point_above_non_upper
    {reachable : Carrier → Prop} {least lower : Carrier}
    (leastMinimal : ∀ upper,
      Problib.Real.IsUpperBound Dedekind.le reachable upper →
        Dedekind.le least upper)
    (lowerLeast : Dedekind.lt lower least) :
    ∃ point, reachable point ∧ Dedekind.lt lower point := by
  have notUpper :
      ¬Problib.Real.IsUpperBound Dedekind.le reachable lower := by
    intro lowerUpper
    exact lowerLeast.2 (leastMinimal lower lowerUpper)
  unfold Problib.Real.IsUpperBound at notUpper
  rcases Classical.not_forall.mp notUpper with ⟨point, pointFailure⟩
  rcases Classical.not_imp.mp pointFailure with ⟨pointReachable, notPointLower⟩
  exact ⟨point, pointReachable,
    ⟨Dedekind.le_of_not_le notPointLower, notPointLower⟩⟩

private theorem combine_prefix_cover
    (intervals : Nat → Carrier × Carrier)
    {left point target : Carrier} {oldBound intervalIndex : Nat}
    (oldCover : Set.Subset (closedInterval left point)
      (Set.prefixUnion (fun index => openInterval (intervals index))
        oldBound))
    (intervalLeftPoint : Dedekind.lt (intervals intervalIndex).1 point)
    (targetIntervalRight : Dedekind.lt target
      (intervals intervalIndex).2) :
    ∃ bound, Set.Subset (closedInterval left target)
      (Set.prefixUnion (fun index => openInterval (intervals index)) bound) := by
  let bound := Nat.max oldBound (intervalIndex + 1)
  refine ⟨bound, ?_⟩
  intro value valueClosed
  by_cases beforePoint : Dedekind.le value point
  · exact prefix_cover_monotone intervals (Nat.le_max_left _ _)
      (oldCover ⟨valueClosed.1, beforePoint⟩)
  · have pointValue : Dedekind.lt point value :=
      ⟨Dedekind.le_of_not_le beforePoint, beforePoint⟩
    have intervalMember : openInterval (intervals intervalIndex) value :=
      ⟨Dedekind.lt_of_lt_of_le intervalLeftPoint pointValue.1,
        Dedekind.lt_of_le_of_lt valueClosed.2 targetIntervalRight⟩
    exact Set.subset_prefixUnion_of_lt _
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self intervalIndex)
        (Nat.le_max_right oldBound (intervalIndex + 1)))
      intervalMember

/-- A countable open-interval cover of a closed interval has a finite prefix
subcover. The proof uses the least upper bound of finitely coverable endpoints. -/
public theorem exists_prefix_cover
    (intervals : Nat → Carrier × Carrier)
    {left right : Carrier} (ordered : Dedekind.le left right)
    (covers : Set.Subset (closedInterval left right)
      (Set.iUnion (fun index => openInterval (intervals index)))) :
    ∃ bound, Set.Subset (closedInterval left right)
      (Set.prefixUnion (fun index => openInterval (intervals index)) bound) := by
  let family : Nat → Set Carrier :=
    fun index => openInterval (intervals index)
  let reachable : Carrier → Prop :=
    fun endpoint =>
      Dedekind.le left endpoint ∧
        Dedekind.le endpoint right ∧
          ∃ bound, Set.Subset (closedInterval left endpoint)
            (Set.prefixUnion family bound)
  have leftCovered : (Set.iUnion family) left :=
    covers ⟨Dedekind.le_refl left, ordered⟩
  rcases leftCovered with ⟨leftIndex, leftInterval⟩
  have leftReachable : reachable left := by
    refine ⟨Dedekind.le_refl left, ordered, leftIndex + 1, ?_⟩
    intro value valueClosed
    have valueLeft : value = left :=
      Dedekind.le_antisymm valueClosed.2 valueClosed.1
    subst value
    exact Set.subset_prefixUnion_succ family leftIndex leftInterval
  have reachableNonempty : ∃ endpoint, reachable endpoint :=
    ⟨left, leftReachable⟩
  have rightUpper :
      Problib.Real.IsUpperBound Dedekind.le reachable right :=
    fun _ member => member.2.1
  have reachableBounded :
      ∃ upper, Problib.Real.IsUpperBound Dedekind.le reachable upper :=
    ⟨right, rightUpper⟩
  rcases Dedekind.exists_lub reachable reachableNonempty reachableBounded with
    ⟨least, leastUpper, leastMinimal⟩
  have leftLeast : Dedekind.le left least :=
    leastUpper left leftReachable
  have leastRight : Dedekind.le least right :=
    leastMinimal right rightUpper
  have rightLeast : Dedekind.le right least := by
    apply Classical.byContradiction
    intro notRightLeast
    have leastRightStrict : Dedekind.lt least right :=
      ⟨leastRight, notRightLeast⟩
    have leastCovered : (Set.iUnion family) least :=
      covers ⟨leftLeast, leastRight⟩
    rcases leastCovered with ⟨intervalIndex, intervalAtLeast⟩
    rcases point_above_non_upper leastMinimal intervalAtLeast.1 with
      ⟨point, pointReachable, intervalLeftPoint⟩
    obtain ⟨target, leastTarget, targetRight, targetIntervalRight⟩ :
        ∃ target, Dedekind.lt least target ∧
          Dedekind.le target right ∧
            Dedekind.lt target (intervals intervalIndex).2 := by
      rcases Dedekind.le_total right (intervals intervalIndex).2 with
        rightBeforeInterval | intervalBeforeRight
      · rcases Dedekind.exists_rational_between leastRightStrict with
          ⟨rational, leastTarget, targetBeforeRight⟩
        exact ⟨Dedekind.selection.ofRat rational, leastTarget,
          targetBeforeRight.1,
          Dedekind.lt_of_lt_of_le targetBeforeRight rightBeforeInterval⟩
      · rcases Dedekind.exists_rational_between intervalAtLeast.2 with
          ⟨rational, leastTarget, targetBeforeInterval⟩
        exact ⟨Dedekind.selection.ofRat rational, leastTarget,
          Dedekind.le_trans targetBeforeInterval.1 intervalBeforeRight,
          targetBeforeInterval⟩
    rcases pointReachable with ⟨_, _, oldBound, oldCover⟩
    rcases combine_prefix_cover intervals oldCover intervalLeftPoint
      targetIntervalRight with ⟨bound, targetCover⟩
    have targetReachable : reachable target :=
      ⟨Dedekind.lt_of_le_of_lt leftLeast leastTarget |>.1, targetRight,
        bound, targetCover⟩
    exact leastTarget.2 (leastUpper target targetReachable)
  have leastRightEqual : least = right :=
    Dedekind.le_antisymm leastRight rightLeast
  have rightCovered : (Set.iUnion family) right :=
    covers ⟨ordered, Dedekind.le_refl right⟩
  rcases rightCovered with ⟨intervalIndex, intervalAtRight⟩
  have intervalLeftLeast : Dedekind.lt (intervals intervalIndex).1 least := by
    rw [leastRightEqual]
    exact intervalAtRight.1
  rcases point_above_non_upper leastMinimal intervalLeftLeast with
    ⟨point, pointReachable, intervalLeftPoint⟩
  rcases pointReachable with ⟨_, _, oldBound, oldCover⟩
  exact combine_prefix_cover intervals oldCover intervalLeftPoint intervalAtRight.2

end Problib.Measure.Real.Compact
