module

public import Foundations.Measure.Real.Interval

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kexing Ying

Statements and proof structure are adapted from
Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35. Tiny uses only its explicit
Dedekind order and generated measurable spaces.
-/

set_option autoImplicit false

namespace Foundations.Measure.Real

open Foundations.Real.Construction

universe u

@[expose] public def halfOpenIntervals : Set (Set Carrier) :=
  fun set => ∃ lower upper, set = Ioc lower upper

@[expose] public def borel : Space Carrier :=
  Space.generated halfOpenIntervals

public theorem measurable_Ioc (lower upper : Carrier) :
    borel.Measurable (Ioc lower upper) :=
  Space.generated_contains ⟨lower, upper, rfl⟩

private def naturalUpperRay (lower : Carrier) (index : Nat) : Set Carrier :=
  Ioc lower (Dedekind.selection.ofRat (index : Rat))

private theorem Ioi_eq_iUnion_naturalUpperRay (lower : Carrier) :
    Ioi lower = Set.iUnion (naturalUpperRay lower) := by
  apply Set.ext
  intro value
  constructor
  · intro lowerLess
    rcases Dedekind.existsNatUpper value with ⟨index, valueLe⟩
    exact ⟨index, lowerLess, valueLe⟩
  · rintro ⟨index, member⟩
    exact member.1

public theorem measurable_Ioi (lower : Carrier) :
    borel.Measurable (Ioi lower) := by
  rw [Ioi_eq_iUnion_naturalUpperRay]
  exact borel.iUnion fun index => measurable_Ioc lower _

public theorem measurable_Iic (upper : Carrier) :
    borel.Measurable (Iic upper) := by
  rw [← complementIoi]
  exact borel.complement (measurable_Ioi upper)

private noncomputable def approachBelow (boundary : Carrier) (index : Nat) : Carrier :=
  Dedekind.sub boundary
    (Dedekind.inverse
      (Dedekind.selection.ofRat (Nat.succ index : Rat)))

private theorem embeddedSuccessorPositive (index : Nat) :
    Dedekind.lt Dedekind.zero
      (Dedekind.selection.ofRat (Nat.succ index : Rat)) := by
  rw [← Dedekind.ofRatZero]
  apply (Dedekind.ofRatLtIff 0 (Nat.succ index : Rat)).mpr
  exact Rat.natCast_pos.mpr (Nat.zero_lt_succ index)

private theorem approachBelow_lt (boundary : Carrier) (index : Nat) :
    Dedekind.lt (approachBelow boundary index) boundary := by
  let error := Dedekind.inverse
    (Dedekind.selection.ofRat (Nat.succ index : Rat))
  have errorPositive : Dedekind.lt Dedekind.zero error :=
    Dedekind.inverseOfPositivePositive (embeddedSuccessorPositive index)
  have translated := (Dedekind.addLtAddLeftIff
    (left := Dedekind.zero) (right := error)
    (shift := approachBelow boundary index)).mpr errorPositive
  rw [Dedekind.addZero] at translated
  have restored :
      Dedekind.add (approachBelow boundary index) error = boundary := by
    rw [Dedekind.addComm]
    exact addSubCancel boundary error
  rw [restored] at translated
  exact translated

private theorem Iio_eq_iUnion_approachBelow (upper : Carrier) :
    Iio upper = Set.iUnion (fun index => Iic (approachBelow upper index)) := by
  apply Set.ext
  intro value
  constructor
  · intro valueLess
    have gapPositive := ltIffSubPositive.mp valueLess
    rcases Dedekind.existsPositiveInverseBelow gapPositive with
      ⟨index, indexPositive, inverseLess⟩
    cases index with
    | zero =>
        change Dedekind.lt Dedekind.zero
          (Dedekind.selection.ofRat (0 : Rat)) at indexPositive
        rw [Dedekind.ofRatZero] at indexPositive
        exact False.elim (Dedekind.ltIrrefl Dedekind.zero indexPositive)
    | succ predecessor =>
        refine ⟨predecessor, ?_⟩
        have shifted := (ltSubIffAddLt
          (value := Dedekind.inverse
            (Dedekind.selection.ofRat (Nat.succ predecessor : Rat)))
          (upper := upper) (shift := value)).mp inverseLess
        have commuted : Dedekind.lt
            (Dedekind.add
              (Dedekind.inverse
                (Dedekind.selection.ofRat (Nat.succ predecessor : Rat)))
              value) upper := by
          rw [Dedekind.addComm]
          exact shifted
        exact ((ltSubIffAddLt
          (value := value) (upper := upper)
          (shift := Dedekind.inverse
            (Dedekind.selection.ofRat (Nat.succ predecessor : Rat)))).mpr
              commuted).left
  · rintro ⟨index, valueLe⟩
    exact ltOfLeOfLt valueLe (approachBelow_lt upper index)

public theorem measurable_Iio (upper : Carrier) :
    borel.Measurable (Iio upper) := by
  rw [Iio_eq_iUnion_approachBelow]
  exact borel.iUnion fun index => measurable_Iic (approachBelow upper index)

/-- Measurability criterion through closed lower rays.
A map into real Borel space is measurable when all closed lower ray
preimages are measurable. -/
public theorem measurableMap_borel_iff_Iic {α : Type u} {source : Space α}
    {function : α → Carrier} :
    MeasurableMap source borel function ↔
      ∀ upper, source.Measurable (Set.preimage function (Iic upper)) := by
  constructor
  · intro measurable upper
    exact measurable (measurable_Iic upper)
  · intro measurable
    apply MeasurableMap.intoGenerated
    rintro set ⟨lower, upper, rfl⟩
    rw [Ioc_eq_difference]
    exact source.difference (measurable upper) (measurable lower)

/-- Measurability criterion through open lower rays.
A map into real Borel space is measurable when all open lower ray
preimages are measurable. -/
public theorem measurableMap_borel_iff_Iio {α : Type u} {source : Space α}
    {function : α → Carrier} :
    MeasurableMap source borel function ↔
      ∀ upper, source.Measurable (Set.preimage function (Iio upper)) := by
  constructor
  · intro measurable upper
    exact measurable (measurable_Iio upper)
  · intro measurable
    apply measurableMap_borel_iff_Iic.mpr
    intro upper
    have same : Set.preimage function (Iic upper) = Set.iInter
        (fun index => Set.preimage function
          (Iio (Dedekind.neg (approachBelow (Dedekind.neg upper) index)))) := by
      apply Set.ext
      intro value
      constructor
      · intro included index
        change Dedekind.lt (function value)
          (Dedekind.neg (approachBelow (Dedekind.neg upper) index))
        have below := ltOfLtOfLe (approachBelow_lt (Dedekind.neg upper) index)
          (Dedekind.negLeNegIff.mpr included)
        simpa only [Dedekind.negNeg] using Dedekind.negLtNegIff.mpr below
      · intro bounded
        apply Classical.byContradiction
        intro missing
        have above := Dedekind.negLtNegIff.mpr (notLeIffLt.mp missing)
        have member : Set.iUnion (fun index => Iic
            (approachBelow (Dedekind.neg upper) index)) (Dedekind.neg (function value)) := by
          rw [← Iio_eq_iUnion_approachBelow]
          exact above
        rcases member with ⟨index, included⟩
        apply (bounded index).2
        simpa only [Dedekind.negNeg] using Dedekind.negLeNegIff.mpr included
    rw [same]
    exact source.iInter fun index => measurable _

public theorem measurable_Ici (lower : Carrier) :
    borel.Measurable (Ici lower) := by
  rw [← complementIio]
  exact borel.complement (measurable_Iio lower)

public theorem measurable_Ioo (lower upper : Carrier) :
    borel.Measurable (Ioo lower upper) := by
  rw [Ioo_eq_inter]
  exact borel.inter (measurable_Ioi lower) (measurable_Iio upper)

public theorem measurable_Ico (lower upper : Carrier) :
    borel.Measurable (Ico lower upper) := by
  rw [Ico_eq_inter]
  exact borel.inter (measurable_Ici lower) (measurable_Iio upper)

public theorem measurable_Icc (lower upper : Carrier) :
    borel.Measurable (Icc lower upper) := by
  rw [Icc_eq_inter]
  exact borel.inter (measurable_Ici lower) (measurable_Iic upper)

@[expose] public def IsLowerSet (set : Set Carrier) : Prop :=
  ∀ ⦃lower upper⦄, Dedekind.le lower upper → set upper → set lower

public theorem measurable_lowerSet {set : Set Carrier}
    (lowerSet : IsLowerSet set) : borel.Measurable set := by
  classical
  by_cases nonempty : Set.Nonempty set
  · by_cases bounded :
        ∃ upper, Foundations.Real.IsUpperBound Dedekind.le set upper
    · rcases Dedekind.existsLub set nonempty bounded with
        ⟨boundary, boundaryUpper, boundaryLeast⟩
      by_cases boundaryMember : set boundary
      · have equal : set = Iic boundary := by
          apply Set.ext
          intro value
          constructor
          · exact boundaryUpper value
          · intro valueLe
            exact lowerSet valueLe boundaryMember
        rw [equal]
        exact measurable_Iic boundary
      · have equal : set = Iio boundary := by
          apply Set.ext
          intro value
          constructor
          · intro valueMember
            have valueLe := boundaryUpper value valueMember
            refine ⟨valueLe, ?_⟩
            intro boundaryLe
            have valueEqual := Dedekind.leAntisymm valueLe boundaryLe
            exact boundaryMember (valueEqual ▸ valueMember)
          · intro valueLess
            by_cases valueMember : set value
            · exact valueMember
            · have valueUpper :
                  Foundations.Real.IsUpperBound Dedekind.le set value := by
                intro candidate candidateMember
                rcases Dedekind.leTotal candidate value with included | reverse
                · exact included
                · by_cases included : Dedekind.le candidate value
                  · exact included
                  · exact False.elim
                      (valueMember (lowerSet reverse candidateMember))
              exact False.elim
                (valueLess.right (boundaryLeast value valueUpper))
        rw [equal]
        exact measurable_Iio boundary
    · have equal : set = Set.univ := by
        apply Set.ext
        intro value
        constructor
        · intro _
          exact True.intro
        · intro _
          by_cases valueMember : set value
          · exact valueMember
          · have valueUpper :
                Foundations.Real.IsUpperBound Dedekind.le set value := by
              intro candidate candidateMember
              rcases Dedekind.leTotal candidate value with included | reverse
              · exact included
              · by_cases included : Dedekind.le candidate value
                · exact included
                · exact False.elim
                    (valueMember (lowerSet reverse candidateMember))
            exact False.elim (bounded ⟨value, valueUpper⟩)
      rw [equal]
      exact borel.univ
  · have equal : set = Set.empty := by
      apply Set.ext
      intro value
      exact ⟨fun member => nonempty ⟨value, member⟩, False.elim⟩
    rw [equal]
    exact borel.empty

@[expose] public def Monotone (function : Carrier → Carrier) : Prop :=
  ∀ ⦃left right⦄, Dedekind.le left right →
    Dedekind.le (function left) (function right)

/-- Measurability of an output function that is monotone relative to a
measurable real coordinate.
For each threshold, the proof forms an ambient real lower set by downward
closure of source coordinates and pulls it back along the coordinate. -/
public theorem monotone_pullback_measurable {α : Type u} {source : Space α}
    {coordinate function : α → Carrier}
    (coordinateMeasurable : MeasurableMap source borel coordinate)
    (monotone : ∀ ⦃left right⦄, Dedekind.le (coordinate left) (coordinate right) →
      Dedekind.le (function left) (function right)) :
    MeasurableMap source borel function := by
  apply measurableMap_borel_iff_Iic.mpr
  intro upper
  let lower : Set Carrier := fun point =>
    ∃ value : α, Dedekind.le point (coordinate value) ∧
      Dedekind.le (function value) upper
  have lowerSet : IsLowerSet lower := by
    intro left right included
    rintro ⟨value, above, below⟩
    exact ⟨value, Dedekind.leTrans included above, below⟩
  have preimageEqual : Set.preimage function (Iic upper) =
      Set.preimage coordinate lower := by
    apply Set.ext
    intro value
    constructor
    · intro member
      exact ⟨value, Dedekind.leRefl _, member⟩
    · rintro ⟨other, included, bounded⟩
      exact Dedekind.leTrans (monotone included) bounded
  rw [preimageEqual]
  exact coordinateMeasurable (measurable_lowerSet lowerSet)

public theorem monotone_measurable {function : Carrier → Carrier}
    (monotone : Monotone function) :
    MeasurableMap borel borel function :=
  monotone_pullback_measurable (MeasurableMap.identity borel) monotone

@[expose] public def unitSet : Set Carrier :=
  Icc Dedekind.zero Dedekind.one

public abbrev UnitInterval := { value : Carrier // unitSet value }

@[expose] public def unitZero : UnitInterval :=
  ⟨Dedekind.zero, Dedekind.leRefl _, Dedekind.oneNonnegative⟩

@[expose] public noncomputable def unitOne : UnitInterval :=
  ⟨Dedekind.one, Dedekind.oneNonnegative, Dedekind.leRefl _⟩

@[expose] public def unitInclusion (value : UnitInterval) : Carrier :=
  value.val

@[expose] public def unitBorel : Space UnitInterval :=
  Space.comap unitInclusion borel

public theorem unitInclusionMeasurable :
    MeasurableMap unitBorel borel unitInclusion :=
  Space.comap_map unitInclusion borel

/-- Measurability criterion for maps into unit Borel space.
A map into `unitBorel` is measurable when preimages of open lower rays
under value inclusion are measurable. -/
public theorem measurableMap_unitBorel_iff_Iio {α : Type u} {source : Space α}
    {function : α → UnitInterval} :
    MeasurableMap source unitBorel function ↔
      ∀ upper, source.Measurable (fun value => Dedekind.lt (function value).val upper) := by
  constructor
  · intro measurable upper
    exact measurable (unitInclusionMeasurable (measurable_Iio upper))
  · intro measurable
    have inclusion : MeasurableMap source borel (fun value => (function value).val) :=
      measurableMap_borel_iff_Iio.mpr measurable
    intro region regionMeasurable
    rcases (Space.comap_measurable_iff unitInclusion borel region).mp regionMeasurable with
      ⟨target, targetMeasurable, rfl⟩
    exact inclusion targetMeasurable

@[expose] public noncomputable def clampValue (value : Carrier) : Carrier := by
  classical
  exact if Dedekind.le value Dedekind.zero then Dedekind.zero
    else if Dedekind.le Dedekind.one value then Dedekind.one else value

public theorem clampValue_nonnegative (value : Carrier) :
    Dedekind.le Dedekind.zero (clampValue value) := by
  classical
  unfold clampValue
  by_cases low : Dedekind.le value Dedekind.zero
  · rw [if_pos low]
    exact Dedekind.leRefl Dedekind.zero
  · rw [if_neg low]
    by_cases high : Dedekind.le Dedekind.one value
    · rw [if_pos high]
      exact Dedekind.oneNonnegative
    · rw [if_neg high]
      rcases Dedekind.leTotal Dedekind.zero value with included | reverse
      · exact included
      · exact False.elim (low reverse)

public theorem clampValue_le_one (value : Carrier) :
    Dedekind.le (clampValue value) Dedekind.one := by
  classical
  unfold clampValue
  by_cases low : Dedekind.le value Dedekind.zero
  · rw [if_pos low]
    exact Dedekind.oneNonnegative
  · rw [if_neg low]
    by_cases high : Dedekind.le Dedekind.one value
    · rw [if_pos high]
      exact Dedekind.leRefl Dedekind.one
    · rw [if_neg high]
      rcases Dedekind.leTotal value Dedekind.one with included | reverse
      · exact included
      · exact False.elim (high reverse)

public theorem clampValue_of_mem {value : Carrier} (member : unitSet value) :
    clampValue value = value := by
  classical
  unfold unitSet at member
  unfold clampValue
  by_cases low : Dedekind.le value Dedekind.zero
  · rw [if_pos low]
    exact Dedekind.leAntisymm member.1 low
  · rw [if_neg low]
    by_cases high : Dedekind.le Dedekind.one value
    · rw [if_pos high]
      exact (Dedekind.leAntisymm member.2 high).symm
    · rw [if_neg high]

public theorem clampValue_monotone : Monotone clampValue := by
  intro left right included
  classical
  by_cases leftLow : Dedekind.le left Dedekind.zero
  · rw [show clampValue left = Dedekind.zero by
      unfold clampValue; rw [if_pos leftLow]]
    exact clampValue_nonnegative right
  · by_cases rightHigh : Dedekind.le Dedekind.one right
    · rw [show clampValue right = Dedekind.one by
        unfold clampValue; rw [if_neg (fun rightLow =>
          leftLow (Dedekind.leTrans included rightLow)), if_pos rightHigh]]
      exact clampValue_le_one left
    · have rightNotLow : ¬Dedekind.le right Dedekind.zero := fun rightLow =>
        leftLow (Dedekind.leTrans included rightLow)
      have leftNotHigh : ¬Dedekind.le Dedekind.one left := fun leftHigh =>
        rightHigh (Dedekind.leTrans leftHigh included)
      rw [show clampValue left = left by
          unfold clampValue; rw [if_neg leftLow, if_neg leftNotHigh],
        show clampValue right = right by
          unfold clampValue; rw [if_neg rightNotLow, if_neg rightHigh]]
      exact included

public theorem clampValueMeasurable :
    MeasurableMap borel borel clampValue :=
  monotone_measurable clampValue_monotone

@[expose] public noncomputable def clamp01 (value : Carrier) : UnitInterval :=
  ⟨clampValue value, clampValue_nonnegative value, clampValue_le_one value⟩

public theorem clamp01Measurable :
    MeasurableMap borel unitBorel clamp01 := by
  unfold unitBorel Space.comap
  apply MeasurableMap.intoGenerated
  rintro set ⟨target, targetMeasurable, rfl⟩
  exact clampValueMeasurable targetMeasurable

public theorem clamp01_of_mem {value : Carrier} (member : unitSet value) :
    unitInclusion (clamp01 value) = value :=
  clampValue_of_mem member

@[expose] public def unitInitial (upper : UnitInterval) : Set UnitInterval :=
  fun value => Dedekind.le value.val upper.val

public theorem unitInitialMeasurable (upper : UnitInterval) :
    unitBorel.Measurable (unitInitial upper) :=
  unitInclusionMeasurable (measurable_Iic upper.val)

public theorem unitInitial_one : unitInitial unitOne = Set.univ := by
  apply Set.ext
  intro value
  exact ⟨fun _ => True.intro, fun _ => value.property.2⟩

public theorem existsUnitRightBelow (point : UnitInterval) (upper : Carrier)
    (room : Dedekind.lt point.val Dedekind.one)
    (below : Dedekind.lt point.val upper) :
    ∃ right : UnitInterval, Dedekind.lt point.val right.val ∧ Dedekind.lt right.val upper := by
  rcases Dedekind.leTotal upper Dedekind.one with upperInside | oneBelow
  · rcases Dedekind.existsRationalBetween below with ⟨rational, above, less⟩
    exact ⟨⟨Dedekind.selection.ofRat rational, Dedekind.leTrans point.property.1 above.1,
      Dedekind.leTrans less.1 upperInside⟩, above, less⟩
  · rcases Dedekind.existsRationalBetween room with ⟨rational, above, less⟩
    exact ⟨⟨Dedekind.selection.ofRat rational, Dedekind.leTrans point.property.1 above.1,
      less.1⟩, above, ltOfLtOfLe less oneBelow⟩

public theorem unitMonotone_measurable {function : UnitInterval → UnitInterval}
    (monotone : ∀ {left right}, Dedekind.le left.val right.val →
      Dedekind.le (function left).val (function right).val) :
    MeasurableMap unitBorel unitBorel function := by
  have ambient : MeasurableMap borel borel
      (fun value => (function (clamp01 value)).val) :=
    monotone_measurable (fun {_ _} included =>
      monotone (clampValue_monotone included))
  have extended : MeasurableMap borel unitBorel
      (fun value => function (clamp01 value)) := by
    unfold unitBorel Space.comap
    apply MeasurableMap.intoGenerated
    rintro set ⟨target, measurable, rfl⟩
    exact ambient measurable
  have restricted : MeasurableMap unitBorel unitBorel
      (fun value => function (clamp01 (unitInclusion value))) :=
    MeasurableMap.comp extended unitInclusionMeasurable
  have same : (fun value : UnitInterval =>
      function (clamp01 (unitInclusion value))) = function := by
    apply funext
    intro value
    apply congrArg function
    apply Subtype.ext
    exact clamp01_of_mem value.property
  exact same ▸ @restricted

end Foundations.Measure.Real
