module

public import Problib.Measure.Real.Cover.Cost
public import Problib.Measure.Real.Compact.Length
public import Problib.Measure.Outer

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov

Adapted from Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny enlarges a countable half-open cover, extracts a finite open subcover,
and accounts explicitly for target shrinkage and cover enlargement.
-/

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction

public section

/-- A countable cover by ordered half-open intervals. -/
public structure IntervalCover (set : Set Carrier) where
  lower : Nat → Carrier
  upper : Nat → Carrier
  ordered : ∀ index, Dedekind.le (lower index) (upper index)
  covers : Set.Subset set
    (Set.iUnion (fun index => Ioc (lower index) (upper index)))

namespace IntervalCover

@[expose] public noncomputable def cost {set : Set Carrier}
    (cover : IntervalCover set) : ENNReal :=
  ENNReal.tsum
    (fun index => intervalLength (cover.lower index) (cover.upper index))

@[expose] public def toCountableCover {set : Set Carrier}
    (cover : IntervalCover set) : CountableCover set where
  sets := fun index => Ioc (cover.lower index) (cover.upper index)
  covers := cover.covers

public theorem coverCost_toCountableCover {set : Set Carrier}
    (cover : IntervalCover set) :
    coverCost intervalCost cover.toCountableCover = cover.cost := by
  unfold coverCost cost
  apply ENNReal.tsum_congr
  intro index
  exact intervalCost_ioc _ _

end IntervalCover

private theorem ennreal_lt_trans {first second third : ENNReal}
    (firstSecond : ENNReal.lt first second)
    (secondThird : ENNReal.lt second third) : ENNReal.lt first third := by
  refine ⟨ENNReal.le_trans firstSecond.1 secondThird.1, ?_⟩
  intro thirdFirst
  exact secondThird.2 (ENNReal.le_trans thirdFirst firstSecond.1)

private theorem ennreal_lt_of_lt_of_le {first second third : ENNReal}
    (firstSecond : ENNReal.lt first second)
    (secondThird : ENNReal.le second third) : ENNReal.lt first third := by
  refine ⟨ENNReal.le_trans firstSecond.1 secondThird, ?_⟩
  intro thirdFirst
  exact firstSecond.2 (ENNReal.le_trans secondThird thirdFirst)

private theorem min_positive {left right : ENNReal}
    (leftPositive : ENNReal.lt ENNReal.zero left)
    (rightPositive : ENNReal.lt ENNReal.zero right) :
    ENNReal.lt ENNReal.zero (ENNReal.min left right) := by
  rcases ENNReal.le_total left right with included | included
  · rw [ENNReal.min_eq_left included]
    exact leftPositive
  · rw [ENNReal.min_eq_right included]
    exact rightPositive

private theorem sub_add_right (upper error lower : Carrier) :
    Dedekind.sub (Dedekind.add upper error) lower =
      Dedekind.add (Dedekind.sub upper lower) error := by
  simp only [Dedekind.sub_eq_add_neg]
  calc
    Dedekind.add (Dedekind.add upper error) (Dedekind.neg lower) =
        Dedekind.add upper
          (Dedekind.add error (Dedekind.neg lower)) :=
      Dedekind.add_assoc _ _ _
    _ = Dedekind.add upper
        (Dedekind.add (Dedekind.neg lower) error) := by
      rw [Dedekind.add_comm error]
    _ = Dedekind.add
        (Dedekind.add upper (Dedekind.neg lower)) error :=
      (Dedekind.add_assoc _ _ _).symm

private theorem sub_shift_decompose (upper lower error : Carrier) :
    Dedekind.sub upper lower =
      Dedekind.add
        (Dedekind.sub upper (Dedekind.add lower error)) error := by
  simp only [Dedekind.sub_eq_add_neg]
  symm
  calc
    Dedekind.add
        (Dedekind.add upper (Dedekind.neg (Dedekind.add lower error)))
        error =
      Dedekind.add
        (Dedekind.add upper
          (Dedekind.add (Dedekind.neg lower) (Dedekind.neg error)))
        error := by
      rw [Dedekind.neg_add]
    _ = Dedekind.add upper
        (Dedekind.add
          (Dedekind.add (Dedekind.neg lower) (Dedekind.neg error))
          error) := Dedekind.add_assoc _ _ _
    _ = Dedekind.add upper
        (Dedekind.add (Dedekind.neg lower)
          (Dedekind.add (Dedekind.neg error) error)) := by
      rw [Dedekind.add_assoc]
    _ = Dedekind.add upper
        (Dedekind.add (Dedekind.neg lower) Dedekind.zero) := by
      rw [Dedekind.add_comm (Dedekind.neg error) error,
        Dedekind.add_neg]
    _ = Dedekind.add upper (Dedekind.neg lower) := by
      rw [Dedekind.add_zero]

private theorem intervalLength_positive {lower upper : Carrier}
    (less : Dedekind.lt lower upper) :
    ENNReal.lt ENNReal.zero (intervalLength lower upper) := by
  unfold intervalLength
  have differencePositive := lt_iff_sub_positive.mp less
  have converted := ENNReal.ofReal_lt_ofReal_iff
    (Dedekind.le_refl Dedekind.zero) differencePositive.1
  rw [ENNReal.ofReal_zero] at converted
  exact converted.mpr differencePositive

private theorem add_strict_right {value error : Carrier}
    (positive : Dedekind.lt Dedekind.zero error) :
    Dedekind.lt value (Dedekind.add value error) := by
  have shifted := (Dedekind.add_lt_add_left_iff
    (left := Dedekind.zero) (right := error) (shift := value)).mpr positive
  simpa only [Dedekind.add_zero] using shifted

private theorem intervalLength_le_intervalCover_of_strict
    {lower upper : Carrier} (less : Dedekind.lt lower upper)
    (cover : IntervalCover (Ioc lower upper)) :
    ENNReal.le (intervalLength lower upper) cover.cost := by
  apply ENNReal.le_of_forall_positive_le_add
  intro epsilon epsilonPositive
  cases epsilon with
  | top =>
      rw [ENNReal.add_top]
      exact ENNReal.le_top _
  | finite epsilonValue =>
      let epsilonValueE : ENNReal := ENNReal.finite epsilonValue
      let halfError := ENNReal.half epsilonValueE
      have halfFinite : ENNReal.Finite halfError :=
        ENNReal.half_finite.mpr True.intro
      have halfPositive : ENNReal.lt ENNReal.zero halfError :=
        ENNReal.half_positive epsilonPositive
      let targetHalf := ENNReal.half (intervalLength lower upper)
      have targetFinite : ENNReal.Finite (intervalLength lower upper) :=
        ENNReal.ofReal_finite _
      have targetPositive := intervalLength_positive less
      have targetHalfFinite : ENNReal.Finite targetHalf :=
        ENNReal.half_finite.mpr targetFinite
      have targetHalfPositive : ENNReal.lt ENNReal.zero targetHalf :=
        ENNReal.half_positive targetPositive
      let budget := ENNReal.min halfError targetHalf
      have budgetFinite : ENNReal.Finite budget :=
        ENNReal.finite_of_le (rightFinite := halfFinite) (ENNReal.min_le_left _ _)
      have budgetPositive : ENNReal.lt ENNReal.zero budget :=
        min_positive halfPositive targetHalfPositive
      have budgetRealPositive : Dedekind.lt Dedekind.zero
          (ENNReal.toReal budget) := by
        have converted := (ENNReal.toReal_lt_toReal_iff
          (left := ENNReal.zero) (right := budget) True.intro budgetFinite).mpr
          budgetPositive
        rw [ENNReal.toReal_zero] at converted
        exact converted
      rcases Dedekind.exists_positive_inverse_below budgetRealPositive with
        ⟨index, denominatorPositive, deltaBudget⟩
      let delta := Dedekind.inverse
        (Dedekind.selection.ofRat (index : Rat))
      have deltaPositive : Dedekind.lt Dedekind.zero delta :=
        Dedekind.inverse_of_positive_positive denominatorPositive
      have deltaCostLess : ENNReal.lt (ENNReal.ofReal delta) budget := by
        have converted := (ENNReal.ofReal_lt_ofReal_iff deltaPositive.1
          (ENNReal.toReal_nonnegative budget)).mpr deltaBudget
        rw [ENNReal.ofReal_toReal budgetFinite] at converted
        exact converted
      have deltaCostHalf : ENNReal.le (ENNReal.ofReal delta) halfError :=
        ENNReal.le_trans deltaCostLess.1 (ENNReal.min_le_left _ _)
      have deltaCostTarget : ENNReal.lt (ENNReal.ofReal delta)
          (intervalLength lower upper) :=
        ennreal_lt_trans
          (ennreal_lt_of_lt_of_le deltaCostLess (ENNReal.min_le_right _ _))
          (ENNReal.half_lt_self_of_positive_of_finite targetPositive targetFinite)
      have differenceNonnegative := Dedekind.sub_nonnegative less.1
      have deltaDifference : Dedekind.lt delta
          (Dedekind.sub upper lower) :=
        (ENNReal.ofReal_lt_ofReal_iff deltaPositive.1
          differenceNonnegative).mp deltaCostTarget
      have shiftedLess : Dedekind.lt (Dedekind.add lower delta) upper :=
        lt_sub_iff_add_lt.mp deltaDifference
      rcases ENNReal.exists_positive_summable_error halfError halfFinite
          halfPositive with ⟨errors, errorsPositive, errorsTotal⟩
      have errorsFinite (index : Nat) : ENNReal.Finite (errors index) :=
        ENNReal.finite_of_le (rightFinite := halfFinite)
          (ENNReal.le_trans (ENNReal.term_le_tsum errors index) errorsTotal)
      let errorReal : Nat → Carrier :=
        fun index => ENNReal.toReal (errors index)
      have errorRealPositive (index : Nat) :
          Dedekind.lt Dedekind.zero (errorReal index) := by
        have converted := (ENNReal.toReal_lt_toReal_iff
          (left := ENNReal.zero) (right := errors index)
          True.intro (errorsFinite index)).mpr (errorsPositive index)
        rw [ENNReal.toReal_zero] at converted
        exact converted
      let expandedRight : Nat → Carrier :=
        fun index => Dedekind.add (cover.upper index) (errorReal index)
      have expandedCover : Set.Subset
          (Compact.closedInterval (Dedekind.add lower delta) upper)
          (Set.iUnion (fun index => Compact.openInterval
            (cover.lower index, expandedRight index))) := by
        intro value member
        have targetMember : Ioc lower upper value :=
          ⟨Dedekind.lt_of_lt_of_le (add_strict_right deltaPositive) member.1, member.2⟩
        rcases cover.covers targetMember with ⟨index, intervalMember⟩
        exact ⟨index, intervalMember.1,
          Dedekind.lt_of_le_of_lt intervalMember.2
            (add_strict_right (errorRealPositive index))⟩
      rcases Compact.exists_prefix_cover
          (fun index => (cover.lower index, expandedRight index))
          shiftedLess.1 expandedCover with ⟨bound, prefixCover⟩
      have finiteBound := Compact.finite_open_cover_length_of_endpoints
        cover.lower expandedRight bound prefixCover
      have expandedLength (index : Nat) :
          ENNReal.ofReal
              (Dedekind.sub (expandedRight index) (cover.lower index)) =
            ENNReal.add
              (intervalLength (cover.lower index) (cover.upper index))
              (errors index) := by
        unfold expandedRight errorReal intervalLength
        rw [sub_add_right,
          ENNReal.ofReal_add (Dedekind.sub_nonnegative (cover.ordered index))
            (ENNReal.toReal_nonnegative (errors index)),
          ENNReal.ofReal_toReal (errorsFinite index)]
      have prefixBound : ENNReal.le
          (ENNReal.ofReal
            (Dedekind.sub upper (Dedekind.add lower delta)))
          (ENNReal.add cover.cost halfError) := by
        refine ENNReal.le_trans finiteBound ?_
        rw [ENNReal.partialSum_congr expandedLength,
          ENNReal.partialSum_add]
        exact ENNReal.add_le_add
          (ENNReal.partialSum_le_tsum _ bound)
          (ENNReal.le_trans (ENNReal.partialSum_le_tsum errors bound)
            errorsTotal)
      have targetDecompose : intervalLength lower upper =
          ENNReal.add
            (ENNReal.ofReal
              (Dedekind.sub upper (Dedekind.add lower delta)))
            (ENNReal.ofReal delta) := by
        unfold intervalLength
        rw [sub_shift_decompose,
          ENNReal.ofReal_add (Dedekind.sub_nonnegative shiftedLess.1) deltaPositive.1]
      rw [targetDecompose]
      exact ENNReal.le_trans
        (ENNReal.add_le_add prefixBound deltaCostHalf)
        (by
          rw [ENNReal.add_assoc, ENNReal.half_add_half]
          exact ENNReal.le_refl _)

public theorem intervalLength_le_intervalCover {lower upper : Carrier}
    (cover : IntervalCover (Ioc lower upper)) :
    ENNReal.le (intervalLength lower upper) cover.cost := by
  by_cases less : Dedekind.lt lower upper
  · exact intervalLength_le_intervalCover_of_strict less cover
  · have zeroLength : intervalLength lower upper = ENNReal.zero := by
      unfold intervalLength
      apply ENNReal.ofReal_eq_zero_iff.mpr
      apply not_lt_iff_le.mp
      intro positive
      exact less (lt_iff_sub_positive.mpr positive)
    rw [zeroLength]
    exact ENNReal.zero_le _

end

end Problib.Measure.Real
