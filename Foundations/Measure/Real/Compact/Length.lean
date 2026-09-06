module

public import Foundations.Measure.Real.Compact
public import Foundations.Real.Series

set_option autoImplicit false

namespace Foundations.Measure.Real.Compact

open Foundations.Real
open Foundations.Real.Construction

local notation "Carrier" => Dedekind.selection.Carrier

private noncomputable def intervalLength
    (interval : Carrier × Carrier) : Foundations.Real.ENNReal :=
  ENNReal.ofReal (Dedekind.sub interval.2 interval.1)

private noncomputable def intervalLengthSum :
    List (Carrier × Carrier) → Foundations.Real.ENNReal
  | [] => ENNReal.zero
  | interval :: intervals =>
      ENNReal.add (intervalLength interval) (intervalLengthSum intervals)

private theorem intervalLengthSumAppend
    (first second : List (Carrier × Carrier)) :
    intervalLengthSum (first ++ second) =
      ENNReal.add (intervalLengthSum first) (intervalLengthSum second) := by
  induction first with
  | nil => simp [intervalLengthSum, ENNReal.zeroAdd]
  | cons interval first induction =>
      simp only [List.cons_append, intervalLengthSum]
      rw [induction, ENNReal.addAssoc]

private theorem intervalLengthSumExtract
    (before after : List (Carrier × Carrier))
    (interval : Carrier × Carrier) :
    intervalLengthSum (before ++ interval :: after) =
      ENNReal.add (intervalLength interval)
        (intervalLengthSum (before ++ after)) := by
  rw [intervalLengthSumAppend, intervalLengthSum,
    intervalLengthSumAppend]
  calc
    ENNReal.add (intervalLengthSum before)
        (ENNReal.add (intervalLength interval) (intervalLengthSum after)) =
      ENNReal.add (intervalLength interval)
        (ENNReal.add (intervalLengthSum before) (intervalLengthSum after)) :=
      by
        rw [← ENNReal.addAssoc,
          ENNReal.addComm (intervalLengthSum before) (intervalLength interval),
          ENNReal.addAssoc]

private theorem subNonnegative {left right : Carrier}
    (included : Dedekind.le left right) :
    Dedekind.le Dedekind.zero (Dedekind.sub right left) :=
  Dedekind.additive.linearlyOrderedGroup.subNonnegativeOfLe included

private theorem subNonpositive {left right : Carrier}
    (included : Dedekind.le right left) :
    Dedekind.le (Dedekind.sub right left) Dedekind.zero := by
  have shifted := (Dedekind.addLeAddRightIff
    (left := right) (right := left) (shift := Dedekind.neg left)).mpr included
  have shiftedSub : Dedekind.le
      (Dedekind.sub right left) (Dedekind.sub left left) := by
    simpa only [← Dedekind.subEqAddNeg] using shifted
  have selfZero : Dedekind.sub left left = Dedekind.zero := by
    rw [Dedekind.subEqAddNeg, Dedekind.addNeg]
  rw [selfZero] at shiftedSub
  exact shiftedSub

private theorem leOfNotLe {left right : Carrier}
    (notReverse : ¬Dedekind.le right left) : Dedekind.le left right := by
  rcases Dedekind.leTotal left right with included | reverse
  · exact included
  · exact False.elim (notReverse reverse)

private theorem subLeSub {firstLeft firstRight secondLeft secondRight : Carrier}
    (leftIncluded : Dedekind.le secondLeft firstLeft)
    (rightIncluded : Dedekind.le firstRight secondRight) :
    Dedekind.le (Dedekind.sub firstRight firstLeft)
      (Dedekind.sub secondRight secondLeft) := by
  rw [Dedekind.subEqAddNeg, Dedekind.subEqAddNeg]
  exact Dedekind.additive.orderedGroup.addLeAdd rightIncluded
    (Dedekind.additive.orderedGroup.negAntitone leftIncluded)

private theorem subDecompose {left middle right : Carrier} :
    Dedekind.sub right left =
      Dedekind.add (Dedekind.sub middle left)
        (Dedekind.sub right middle) := by
  rw [Dedekind.subEqAddNeg, Dedekind.subEqAddNeg,
    Dedekind.subEqAddNeg]
  symm
  calc
    Dedekind.add
        (Dedekind.add middle (Dedekind.neg left))
        (Dedekind.add right (Dedekind.neg middle)) =
      Dedekind.add
        (Dedekind.add (Dedekind.add middle (Dedekind.neg left)) right)
        (Dedekind.neg middle) :=
      (Dedekind.addAssoc _ _ _).symm
    _ = Dedekind.add
        (Dedekind.add right
          (Dedekind.add middle (Dedekind.neg left)))
        (Dedekind.neg middle) := by
      rw [Dedekind.addComm
        (Dedekind.add middle (Dedekind.neg left)) right]
    _ = Dedekind.add
        (Dedekind.add right
          (Dedekind.add (Dedekind.neg left) middle))
        (Dedekind.neg middle) := by
      rw [Dedekind.addComm middle (Dedekind.neg left)]
    _ = Dedekind.add
        (Dedekind.add (Dedekind.add right (Dedekind.neg left)) middle)
        (Dedekind.neg middle) := by
      rw [← Dedekind.addAssoc]
    _ = Dedekind.add (Dedekind.add right (Dedekind.neg left))
        (Dedekind.add middle (Dedekind.neg middle)) :=
      Dedekind.addAssoc _ _ _
    _ = Dedekind.add (Dedekind.add right (Dedekind.neg left))
        Dedekind.zero := by
      rw [Dedekind.addNeg]
    _ = Dedekind.add right (Dedekind.neg left) :=
      Dedekind.addZero _

private theorem intervalLengthLeSumOfMem
    {interval : Carrier × Carrier}
    {intervals : List (Carrier × Carrier)}
    (member : interval ∈ intervals) :
    ENNReal.le (intervalLength interval) (intervalLengthSum intervals) := by
  induction intervals with
  | nil => simp at member
  | cons head tail induction =>
      rw [List.mem_cons] at member
      cases member with
      | inl equal =>
          subst head
          have included := ENNReal.addLeAdd
            (ENNReal.leRefl (intervalLength interval))
            (ENNReal.zeroLe (intervalLengthSum tail))
          simpa only [intervalLengthSum, ENNReal.addZero] using included
      | inr tailMember =>
          exact ENNReal.leTrans (induction tailMember)
            (by
              have included := ENNReal.addLeAdd
                (ENNReal.zeroLe (intervalLength head))
                (ENNReal.leRefl (intervalLengthSum tail))
              simpa only [intervalLengthSum, ENNReal.zeroAdd] using included)

private theorem finiteOpenCoverLengthList
    (intervals : List (Carrier × Carrier))
    {left right : Carrier}
    (covers : ∀ value, Dedekind.le left value →
      Dedekind.le value right →
        ∃ interval, interval ∈ intervals ∧ openInterval interval value) :
    ENNReal.le (ENNReal.ofReal (Dedekind.sub right left))
      (intervalLengthSum intervals) := by
  by_cases ordered : Dedekind.le left right
  · rcases covers left (Dedekind.leRefl left) ordered with
      ⟨interval, member, intervalAtLeft⟩
    rcases List.mem_iff_append.mp member with
      ⟨before, after, intervalSplit⟩
    by_cases rightBefore : Dedekind.le right interval.2
    · have differenceIncluded : Dedekind.le
          (Dedekind.sub right left)
          (Dedekind.sub interval.2 interval.1) :=
        subLeSub intervalAtLeft.1.1 rightBefore

      exact ENNReal.leTrans (ENNReal.ofRealMonotone differenceIncluded)
        (intervalLengthLeSumOfMem member)
    · have intervalRightBefore : Dedekind.le interval.2 right :=
        leOfNotLe rightBefore
      have remainingCover : ∀ value,
          Dedekind.le interval.2 value → Dedekind.le value right →
            ∃ candidate, candidate ∈ before ++ after ∧
              openInterval candidate value := by
        intro value intervalRightValue valueRight
        rcases covers value
            (Dedekind.leTrans intervalAtLeft.2.1 intervalRightValue)
            valueRight with ⟨candidate, candidateMember, candidateAtValue⟩
        have candidateDifferent : candidate ≠ interval := by
          intro equal
          subst candidate
          exact candidateAtValue.2.2 intervalRightValue
        rw [intervalSplit, List.mem_append, List.mem_cons] at candidateMember
        rcases candidateMember with beforeMember | selectedOrAfter
        · exact ⟨candidate, List.mem_append_left after beforeMember,
            candidateAtValue⟩
        · rcases selectedOrAfter with selected | afterMember
          · exact False.elim (candidateDifferent selected)
          · exact ⟨candidate, List.mem_append_right before afterMember,
              candidateAtValue⟩
      have recursive := finiteOpenCoverLengthList (before ++ after)
        remainingCover
      have leftMiddle : Dedekind.le left interval.2 :=
        intervalAtLeft.2.1
      have firstNonnegative := subNonnegative leftMiddle
      have secondNonnegative := subNonnegative intervalRightBefore
      have decomposed : ENNReal.ofReal (Dedekind.sub right left) =
          ENNReal.add
            (ENNReal.ofReal (Dedekind.sub interval.2 left))
            (ENNReal.ofReal (Dedekind.sub right interval.2)) := by
        rw [subDecompose,
          ENNReal.ofRealAdd firstNonnegative secondNonnegative]
      have firstIncluded : ENNReal.le
          (ENNReal.ofReal (Dedekind.sub interval.2 left))
          (intervalLength interval) :=
        ENNReal.ofRealMonotone
          (subLeSub intervalAtLeft.1.1 (Dedekind.leRefl interval.2))
      rw [decomposed, intervalSplit, intervalLengthSumExtract]
      exact ENNReal.addLeAdd firstIncluded recursive
  · have reverse : Dedekind.le right left :=
      leOfNotLe ordered
    rw [ENNReal.ofRealEqZeroIff.mpr (subNonpositive reverse)]
    exact ENNReal.zeroLe _
termination_by intervals.length
decreasing_by simp [intervalSplit]

private theorem intervalLengthPrefix
    (intervals : Nat → Carrier × Carrier) (bound : Nat) :
    intervalLengthSum (List.map intervals (List.range bound)) =
      ENNReal.partialSum
        (fun index => ENNReal.ofReal
          (Dedekind.sub (intervals index).2 (intervals index).1))
        bound := by
  induction bound with
  | zero => rfl
  | succ bound induction =>
      rw [List.range_succ, List.map_append, intervalLengthSumAppend,
        induction]
      simp only [List.map, intervalLengthSum, ENNReal.addZero,
        ENNReal.partialSum, intervalLength]

public theorem finiteOpenCoverLength
    (intervals : Nat → Carrier × Carrier)
    {left right : Carrier} (bound : Nat)
    (covers : Set.Subset (closedInterval left right)
      (Set.prefixUnion (fun index => openInterval (intervals index)) bound)) :
    ENNReal.le (ENNReal.ofReal (Dedekind.sub right left))
      (ENNReal.partialSum
        (fun index => ENNReal.ofReal
          (Dedekind.sub (intervals index).2 (intervals index).1))
        bound) := by
  rw [← intervalLengthPrefix]
  apply finiteOpenCoverLengthList
  intro value leftValue valueRight
  rcases Set.mem_prefixUnion_iff _ bound value |>.mp
      (covers ⟨leftValue, valueRight⟩) with
    ⟨index, indexBound, intervalMember⟩
  exact ⟨intervals index,
    List.mem_map.mpr ⟨index, List.mem_range.mpr indexBound, rfl⟩,
    intervalMember⟩

public theorem finiteOpenCoverLengthOfEndpoints
    (intervalLeft intervalRight : Nat → Carrier)
    {left right : Carrier} (bound : Nat)
    (covers : Set.Subset (closedInterval left right)
      (Set.prefixUnion
        (fun index => openInterval
          (intervalLeft index, intervalRight index))
        bound)) :
    ENNReal.le (ENNReal.ofReal (Dedekind.sub right left))
      (ENNReal.partialSum
        (fun index => ENNReal.ofReal
          (Dedekind.sub (intervalRight index) (intervalLeft index)))
        bound) :=
  finiteOpenCoverLength
    (fun index => (intervalLeft index, intervalRight index)) bound covers

end Foundations.Measure.Real.Compact
