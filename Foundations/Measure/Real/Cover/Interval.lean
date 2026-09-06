module

public import Foundations.Measure.Real.Cover.Cost
public import Foundations.Measure.Real.Compact.Length
public import Foundations.Measure.Outer

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

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

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
  apply ENNReal.tsumCongr
  intro index
  exact intervalCost_Ioc _ _

end IntervalCover

private theorem ennrealLtTrans {first second third : ENNReal}
    (firstSecond : ENNReal.lt first second)
    (secondThird : ENNReal.lt second third) : ENNReal.lt first third := by
  refine ⟨ENNReal.leTrans firstSecond.1 secondThird.1, ?_⟩
  intro thirdFirst
  exact secondThird.2 (ENNReal.leTrans thirdFirst firstSecond.1)

private theorem ennrealLtOfLtOfLe {first second third : ENNReal}
    (firstSecond : ENNReal.lt first second)
    (secondThird : ENNReal.le second third) : ENNReal.lt first third := by
  refine ⟨ENNReal.leTrans firstSecond.1 secondThird, ?_⟩
  intro thirdFirst
  exact firstSecond.2 (ENNReal.leTrans secondThird thirdFirst)

private theorem minPositive {left right : ENNReal}
    (leftPositive : ENNReal.lt ENNReal.zero left)
    (rightPositive : ENNReal.lt ENNReal.zero right) :
    ENNReal.lt ENNReal.zero (ENNReal.min left right) := by
  rcases ENNReal.leTotal left right with included | included
  · rw [ENNReal.minEqLeft included]
    exact leftPositive
  · rw [ENNReal.minEqRight included]
    exact rightPositive

private theorem subNonnegative {lower upper : Carrier}
    (ordered : Dedekind.le lower upper) :
    Dedekind.le Dedekind.zero (Dedekind.sub upper lower) :=
  Dedekind.additive.linearlyOrderedGroup.subNonnegativeOfLe ordered

private theorem subAddRight (upper error lower : Carrier) :
    Dedekind.sub (Dedekind.add upper error) lower =
      Dedekind.add (Dedekind.sub upper lower) error := by
  simp only [Dedekind.subEqAddNeg]
  calc
    Dedekind.add (Dedekind.add upper error) (Dedekind.neg lower) =
        Dedekind.add upper
          (Dedekind.add error (Dedekind.neg lower)) :=
      Dedekind.addAssoc _ _ _
    _ = Dedekind.add upper
        (Dedekind.add (Dedekind.neg lower) error) := by
      rw [Dedekind.addComm error]
    _ = Dedekind.add
        (Dedekind.add upper (Dedekind.neg lower)) error :=
      (Dedekind.addAssoc _ _ _).symm

private theorem negAddDistrib (left right : Carrier) :
    Dedekind.neg (Dedekind.add left right) =
      Dedekind.add (Dedekind.neg left) (Dedekind.neg right) := by
  exact Foundations.Algebra.AdditiveCommutativeGroupLaws.negAddDistrib
    Dedekind.additive.group left right

private theorem subShiftDecompose (upper lower error : Carrier) :
    Dedekind.sub upper lower =
      Dedekind.add
        (Dedekind.sub upper (Dedekind.add lower error)) error := by
  simp only [Dedekind.subEqAddNeg]
  symm
  calc
    Dedekind.add
        (Dedekind.add upper (Dedekind.neg (Dedekind.add lower error)))
        error =
      Dedekind.add
        (Dedekind.add upper
          (Dedekind.add (Dedekind.neg lower) (Dedekind.neg error)))
        error := by
      rw [negAddDistrib]
    _ = Dedekind.add upper
        (Dedekind.add
          (Dedekind.add (Dedekind.neg lower) (Dedekind.neg error))
          error) := Dedekind.addAssoc _ _ _
    _ = Dedekind.add upper
        (Dedekind.add (Dedekind.neg lower)
          (Dedekind.add (Dedekind.neg error) error)) := by
      rw [Dedekind.addAssoc]
    _ = Dedekind.add upper
        (Dedekind.add (Dedekind.neg lower) Dedekind.zero) := by
      rw [Dedekind.addComm (Dedekind.neg error) error,
        Dedekind.addNeg]
    _ = Dedekind.add upper (Dedekind.neg lower) := by
      rw [Dedekind.addZero]

private theorem intervalLengthPositive {lower upper : Carrier}
    (less : Dedekind.lt lower upper) :
    ENNReal.lt ENNReal.zero (intervalLength lower upper) := by
  unfold intervalLength
  have differencePositive := ltIffSubPositive.mp less
  have converted := ENNReal.ofRealLtOfRealIff
    (Dedekind.leRefl Dedekind.zero) differencePositive.1
  rw [ENNReal.ofRealZero] at converted
  exact converted.mpr differencePositive

private theorem addStrictRight {value error : Carrier}
    (positive : Dedekind.lt Dedekind.zero error) :
    Dedekind.lt value (Dedekind.add value error) := by
  have shifted := (Dedekind.addLtAddLeftIff
    (left := Dedekind.zero) (right := error) (shift := value)).mpr positive
  simpa only [Dedekind.addZero] using shifted

private theorem intervalLength_le_intervalCover_of_strict
    {lower upper : Carrier} (less : Dedekind.lt lower upper)
    (cover : IntervalCover (Ioc lower upper)) :
    ENNReal.le (intervalLength lower upper) cover.cost := by
  apply ENNReal.leOfForallPositiveLeAdd
  intro epsilon epsilonPositive
  cases epsilon with
  | top =>
      rw [ENNReal.addTop]
      exact ENNReal.leTop _
  | finite epsilonValue =>
      let epsilonValueE : ENNReal := ENNReal.finite epsilonValue
      let halfError := ENNReal.half epsilonValueE
      have halfFinite : ENNReal.Finite halfError :=
        ENNReal.halfFinite.mpr True.intro
      have halfPositive : ENNReal.lt ENNReal.zero halfError :=
        ENNReal.halfPositive epsilonPositive
      let targetHalf := ENNReal.half (intervalLength lower upper)
      have targetFinite : ENNReal.Finite (intervalLength lower upper) :=
        ENNReal.ofRealFinite _
      have targetPositive := intervalLengthPositive less
      have targetHalfFinite : ENNReal.Finite targetHalf :=
        ENNReal.halfFinite.mpr targetFinite
      have targetHalfPositive : ENNReal.lt ENNReal.zero targetHalf :=
        ENNReal.halfPositive targetPositive
      let budget := ENNReal.min halfError targetHalf
      have budgetFinite : ENNReal.Finite budget :=
        ENNReal.finiteOfLe (rightFinite := halfFinite) (ENNReal.minLeLeft _ _)
      have budgetPositive : ENNReal.lt ENNReal.zero budget :=
        minPositive halfPositive targetHalfPositive
      have budgetRealPositive : Dedekind.lt Dedekind.zero
          (ENNReal.toReal budget) := by
        have converted := (ENNReal.toRealLtToRealIff
          (left := ENNReal.zero) (right := budget) True.intro budgetFinite).mpr
          budgetPositive
        rw [ENNReal.toRealZero] at converted
        exact converted
      rcases Dedekind.existsPositiveInverseBelow budgetRealPositive with
        ⟨index, denominatorPositive, deltaBudget⟩
      let delta := Dedekind.inverse
        (Dedekind.selection.ofRat (index : Rat))
      have deltaPositive : Dedekind.lt Dedekind.zero delta :=
        Dedekind.inverseOfPositivePositive denominatorPositive
      have deltaCostLess : ENNReal.lt (ENNReal.ofReal delta) budget := by
        have converted := (ENNReal.ofRealLtOfRealIff deltaPositive.1
          (ENNReal.toRealNonnegative budget)).mpr deltaBudget
        rw [ENNReal.ofRealToReal budgetFinite] at converted
        exact converted
      have deltaCostHalf : ENNReal.le (ENNReal.ofReal delta) halfError :=
        ENNReal.leTrans deltaCostLess.1 (ENNReal.minLeLeft _ _)
      have deltaCostTarget : ENNReal.lt (ENNReal.ofReal delta)
          (intervalLength lower upper) :=
        ennrealLtTrans
          (ennrealLtOfLtOfLe deltaCostLess (ENNReal.minLeRight _ _))
          (ENNReal.halfLtSelfOfPositiveOfFinite targetPositive targetFinite)
      have differenceNonnegative := subNonnegative less.1
      have deltaDifference : Dedekind.lt delta
          (Dedekind.sub upper lower) :=
        (ENNReal.ofRealLtOfRealIff deltaPositive.1
          differenceNonnegative).mp deltaCostTarget
      have shiftedLess : Dedekind.lt (Dedekind.add lower delta) upper :=
        ltSubIffAddLt.mp deltaDifference
      rcases ENNReal.existsPositiveSummableError halfError halfFinite
          halfPositive with ⟨errors, errorsPositive, errorsTotal⟩
      have errorsFinite (index : Nat) : ENNReal.Finite (errors index) :=
        ENNReal.finiteOfLe (rightFinite := halfFinite)
          (ENNReal.leTrans (ENNReal.termLeTsum errors index) errorsTotal)
      let errorReal : Nat → Carrier :=
        fun index => ENNReal.toReal (errors index)
      have errorRealPositive (index : Nat) :
          Dedekind.lt Dedekind.zero (errorReal index) := by
        have converted := (ENNReal.toRealLtToRealIff
          (left := ENNReal.zero) (right := errors index)
          True.intro (errorsFinite index)).mpr (errorsPositive index)
        rw [ENNReal.toRealZero] at converted
        exact converted
      let expandedRight : Nat → Carrier :=
        fun index => Dedekind.add (cover.upper index) (errorReal index)
      have expandedCover : Set.Subset
          (Compact.closedInterval (Dedekind.add lower delta) upper)
          (Set.iUnion (fun index => Compact.openInterval
            (cover.lower index, expandedRight index))) := by
        intro value member
        have targetMember : Ioc lower upper value :=
          ⟨ltOfLtOfLe (addStrictRight deltaPositive) member.1, member.2⟩
        rcases cover.covers targetMember with ⟨index, intervalMember⟩
        exact ⟨index, intervalMember.1,
          ltOfLeOfLt intervalMember.2
            (addStrictRight (errorRealPositive index))⟩
      rcases Compact.existsPrefixCover
          (fun index => (cover.lower index, expandedRight index))
          shiftedLess.1 expandedCover with ⟨bound, prefixCover⟩
      have finiteBound := Compact.finiteOpenCoverLengthOfEndpoints
        cover.lower expandedRight bound prefixCover
      have expandedLength (index : Nat) :
          ENNReal.ofReal
              (Dedekind.sub (expandedRight index) (cover.lower index)) =
            ENNReal.add
              (intervalLength (cover.lower index) (cover.upper index))
              (errors index) := by
        unfold expandedRight errorReal intervalLength
        rw [subAddRight,
          ENNReal.ofRealAdd (subNonnegative (cover.ordered index))
            (ENNReal.toRealNonnegative (errors index)),
          ENNReal.ofRealToReal (errorsFinite index)]
      have prefixBound : ENNReal.le
          (ENNReal.ofReal
            (Dedekind.sub upper (Dedekind.add lower delta)))
          (ENNReal.add cover.cost halfError) := by
        refine ENNReal.leTrans finiteBound ?_
        rw [ENNReal.partialSumCongr expandedLength,
          ENNReal.partialSumAdd]
        exact ENNReal.addLeAdd
          (ENNReal.partialSumLeTsum _ bound)
          (ENNReal.leTrans (ENNReal.partialSumLeTsum errors bound)
            errorsTotal)
      have targetDecompose : intervalLength lower upper =
          ENNReal.add
            (ENNReal.ofReal
              (Dedekind.sub upper (Dedekind.add lower delta)))
            (ENNReal.ofReal delta) := by
        unfold intervalLength
        rw [subShiftDecompose,
          ENNReal.ofRealAdd (subNonnegative shiftedLess.1) deltaPositive.1]
      rw [targetDecompose]
      exact ENNReal.leTrans
        (ENNReal.addLeAdd prefixBound deltaCostHalf)
        (by
          rw [ENNReal.addAssoc, ENNReal.halfAddHalf]
          exact ENNReal.leRefl _)

public theorem intervalLength_le_intervalCover {lower upper : Carrier}
    (cover : IntervalCover (Ioc lower upper)) :
    ENNReal.le (intervalLength lower upper) cover.cost := by
  by_cases less : Dedekind.lt lower upper
  · exact intervalLength_le_intervalCover_of_strict less cover
  · have zeroLength : intervalLength lower upper = ENNReal.zero := by
      unfold intervalLength
      apply ENNReal.ofRealEqZeroIff.mpr
      apply notLtIffLe.mp
      intro positive
      exact less (ltIffSubPositive.mpr positive)
    rw [zeroLength]
    exact ENNReal.zeroLe _

end

end Foundations.Measure.Real
