module

public import Problib.Measure.Real.Compact
public import Problib.Real.Series

set_option autoImplicit false

namespace Problib.Measure.Real.Compact

open Problib.Real
open Problib.Real.Construction

local notation "Carrier" => Dedekind.selection.Carrier

private noncomputable def intervalLength
    (interval : Carrier × Carrier) : Problib.Real.ENNReal :=
  ENNReal.ofReal (Dedekind.sub interval.2 interval.1)

private noncomputable def intervalLengthSum :
    List (Carrier × Carrier) → Problib.Real.ENNReal
  | [] => ENNReal.zero
  | interval :: intervals =>
      ENNReal.add (intervalLength interval) (intervalLengthSum intervals)

private theorem intervalLengthSum_append
    (first second : List (Carrier × Carrier)) :
    intervalLengthSum (first ++ second) =
      ENNReal.add (intervalLengthSum first) (intervalLengthSum second) := by
  induction first with
  | nil => simp [intervalLengthSum, ENNReal.zero_add]
  | cons interval first induction =>
      simp only [List.cons_append, intervalLengthSum]
      rw [induction, ENNReal.add_assoc]

private theorem intervalLengthSum_extract
    (before after : List (Carrier × Carrier))
    (interval : Carrier × Carrier) :
    intervalLengthSum (before ++ interval :: after) =
      ENNReal.add (intervalLength interval)
        (intervalLengthSum (before ++ after)) := by
  rw [intervalLengthSum_append, intervalLengthSum,
    intervalLengthSum_append]
  calc
    ENNReal.add (intervalLengthSum before)
        (ENNReal.add (intervalLength interval) (intervalLengthSum after)) =
      ENNReal.add (intervalLength interval)
        (ENNReal.add (intervalLengthSum before) (intervalLengthSum after)) :=
      by
        rw [← ENNReal.add_assoc,
          ENNReal.add_comm (intervalLengthSum before) (intervalLength interval),
          ENNReal.add_assoc]

private theorem sub_nonpositive {left right : Carrier}
    (included : Dedekind.le right left) :
    Dedekind.le (Dedekind.sub right left) Dedekind.zero := by
  have shifted := (Dedekind.add_le_add_right_iff
    (left := right) (right := left) (shift := Dedekind.neg left)).mpr included
  have shiftedSub : Dedekind.le
      (Dedekind.sub right left) (Dedekind.sub left left) := by
    simpa only [← Dedekind.sub_eq_add_neg] using shifted
  have selfZero : Dedekind.sub left left = Dedekind.zero := by
    rw [Dedekind.sub_eq_add_neg, Dedekind.add_neg]
  rw [selfZero] at shiftedSub
  exact shiftedSub

private theorem sub_le_sub {firstLeft firstRight secondLeft secondRight : Carrier}
    (leftIncluded : Dedekind.le secondLeft firstLeft)
    (rightIncluded : Dedekind.le firstRight secondRight) :
    Dedekind.le (Dedekind.sub firstRight firstLeft)
      (Dedekind.sub secondRight secondLeft) := by
  rw [Dedekind.sub_eq_add_neg, Dedekind.sub_eq_add_neg]
  exact Dedekind.additive.orderedGroup.add_le_add rightIncluded
    (Dedekind.additive.orderedGroup.neg_antitone leftIncluded)

private theorem sub_decompose {left middle right : Carrier} :
    Dedekind.sub right left =
      Dedekind.add (Dedekind.sub middle left)
        (Dedekind.sub right middle) := by
  rw [Dedekind.sub_eq_add_neg, Dedekind.sub_eq_add_neg,
    Dedekind.sub_eq_add_neg]
  symm
  calc
    Dedekind.add
        (Dedekind.add middle (Dedekind.neg left))
        (Dedekind.add right (Dedekind.neg middle)) =
      Dedekind.add
        (Dedekind.add (Dedekind.add middle (Dedekind.neg left)) right)
        (Dedekind.neg middle) :=
      (Dedekind.add_assoc _ _ _).symm
    _ = Dedekind.add
        (Dedekind.add right
          (Dedekind.add middle (Dedekind.neg left)))
        (Dedekind.neg middle) := by
      rw [Dedekind.add_comm
        (Dedekind.add middle (Dedekind.neg left)) right]
    _ = Dedekind.add
        (Dedekind.add right
          (Dedekind.add (Dedekind.neg left) middle))
        (Dedekind.neg middle) := by
      rw [Dedekind.add_comm middle (Dedekind.neg left)]
    _ = Dedekind.add
        (Dedekind.add (Dedekind.add right (Dedekind.neg left)) middle)
        (Dedekind.neg middle) := by
      rw [← Dedekind.add_assoc]
    _ = Dedekind.add (Dedekind.add right (Dedekind.neg left))
        (Dedekind.add middle (Dedekind.neg middle)) :=
      Dedekind.add_assoc _ _ _
    _ = Dedekind.add (Dedekind.add right (Dedekind.neg left))
        Dedekind.zero := by
      rw [Dedekind.add_neg]
    _ = Dedekind.add right (Dedekind.neg left) :=
      Dedekind.add_zero _

private theorem intervalLength_le_sum_of_mem
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
          have included := ENNReal.add_le_add
            (ENNReal.le_refl (intervalLength interval))
            (ENNReal.zero_le (intervalLengthSum tail))
          simpa only [intervalLengthSum, ENNReal.add_zero] using included
      | inr tailMember =>
          exact ENNReal.le_trans (induction tailMember)
            (by
              have included := ENNReal.add_le_add
                (ENNReal.zero_le (intervalLength head))
                (ENNReal.le_refl (intervalLengthSum tail))
              simpa only [intervalLengthSum, ENNReal.zero_add] using included)

private theorem finite_open_cover_length_list
    (intervals : List (Carrier × Carrier))
    {left right : Carrier}
    (covers : ∀ value, Dedekind.le left value →
      Dedekind.le value right →
        ∃ interval, interval ∈ intervals ∧ openInterval interval value) :
    ENNReal.le (ENNReal.ofReal (Dedekind.sub right left))
      (intervalLengthSum intervals) := by
  by_cases ordered : Dedekind.le left right
  · rcases covers left (Dedekind.le_refl left) ordered with
      ⟨interval, member, intervalAtLeft⟩
    rcases List.mem_iff_append.mp member with
      ⟨before, after, intervalSplit⟩
    by_cases rightBefore : Dedekind.le right interval.2
    · have differenceIncluded : Dedekind.le
          (Dedekind.sub right left)
          (Dedekind.sub interval.2 interval.1) :=
        sub_le_sub intervalAtLeft.1.1 rightBefore

      exact ENNReal.le_trans (ENNReal.ofReal_monotone differenceIncluded)
        (intervalLength_le_sum_of_mem member)
    · have intervalRightBefore : Dedekind.le interval.2 right :=
        Dedekind.le_of_not_le rightBefore
      have remainingCover : ∀ value,
          Dedekind.le interval.2 value → Dedekind.le value right →
            ∃ candidate, candidate ∈ before ++ after ∧
              openInterval candidate value := by
        intro value intervalRightValue valueRight
        rcases covers value
            (Dedekind.le_trans intervalAtLeft.2.1 intervalRightValue)
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
      have recursive := finite_open_cover_length_list (before ++ after)
        remainingCover
      have leftMiddle : Dedekind.le left interval.2 :=
        intervalAtLeft.2.1
      have firstNonnegative := Dedekind.sub_nonnegative leftMiddle
      have secondNonnegative := Dedekind.sub_nonnegative intervalRightBefore
      have decomposed : ENNReal.ofReal (Dedekind.sub right left) =
          ENNReal.add
            (ENNReal.ofReal (Dedekind.sub interval.2 left))
            (ENNReal.ofReal (Dedekind.sub right interval.2)) := by
        rw [sub_decompose,
          ENNReal.ofReal_add firstNonnegative secondNonnegative]
      have firstIncluded : ENNReal.le
          (ENNReal.ofReal (Dedekind.sub interval.2 left))
          (intervalLength interval) :=
        ENNReal.ofReal_monotone
          (sub_le_sub intervalAtLeft.1.1 (Dedekind.le_refl interval.2))
      rw [decomposed, intervalSplit, intervalLengthSum_extract]
      exact ENNReal.add_le_add firstIncluded recursive
  · have reverse : Dedekind.le right left :=
      Dedekind.le_of_not_le ordered
    rw [ENNReal.ofReal_eq_zero_iff.mpr (sub_nonpositive reverse)]
    exact ENNReal.zero_le _
termination_by intervals.length
decreasing_by simp [intervalSplit]

private theorem interval_length_prefix
    (intervals : Nat → Carrier × Carrier) (bound : Nat) :
    intervalLengthSum (List.map intervals (List.range bound)) =
      ENNReal.partialSum
        (fun index => ENNReal.ofReal
          (Dedekind.sub (intervals index).2 (intervals index).1))
        bound := by
  induction bound with
  | zero => rfl
  | succ bound induction =>
      rw [List.range_succ, List.map_append, intervalLengthSum_append,
        induction]
      simp only [List.map, intervalLengthSum, ENNReal.add_zero,
        ENNReal.partialSum, intervalLength]

public theorem finite_open_cover_length
    (intervals : Nat → Carrier × Carrier)
    {left right : Carrier} (bound : Nat)
    (covers : Set.Subset (closedInterval left right)
      (Set.prefixUnion (fun index => openInterval (intervals index)) bound)) :
    ENNReal.le (ENNReal.ofReal (Dedekind.sub right left))
      (ENNReal.partialSum
        (fun index => ENNReal.ofReal
          (Dedekind.sub (intervals index).2 (intervals index).1))
        bound) := by
  rw [← interval_length_prefix]
  apply finite_open_cover_length_list
  intro value leftValue valueRight
  rcases Set.mem_prefixUnion_iff _ bound value |>.mp
      (covers ⟨leftValue, valueRight⟩) with
    ⟨index, indexBound, intervalMember⟩
  exact ⟨intervals index,
    List.mem_map.mpr ⟨index, List.mem_range.mpr indexBound, rfl⟩,
    intervalMember⟩

public theorem finite_open_cover_length_of_endpoints
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
  finite_open_cover_length
    (fun index => (intervalLeft index, intervalRight index)) bound covers

end Problib.Measure.Real.Compact
