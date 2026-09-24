module

public import Problib.Measure.Real.Interval

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

namespace Problib.Measure.Real

open Problib.Real.Construction

universe u

@[expose] public def halfOpenIntervals : Set (Set Carrier) :=
  fun set => ∃ lower upper, set = Ioc lower upper

@[expose] public def borel : Space Carrier :=
  Space.generated halfOpenIntervals

public theorem measurable_ioc (lower upper : Carrier) :
    borel.Measurable (Ioc lower upper) :=
  Space.generated_contains ⟨lower, upper, rfl⟩

private def naturalUpperRay (lower : Carrier) (index : Nat) : Set Carrier :=
  Ioc lower (Dedekind.selection.ofRat (index : Rat))

private theorem ioi_eq_iUnion_naturalUpperRay (lower : Carrier) :
    Ioi lower = Set.iUnion (naturalUpperRay lower) := by
  apply Set.ext
  intro value
  constructor
  · intro lowerLess
    rcases Dedekind.exists_nat_upper value with ⟨index, valueLe⟩
    exact ⟨index, lowerLess, valueLe⟩
  · rintro ⟨index, member⟩
    exact member.1

public theorem measurable_ioi (lower : Carrier) :
    borel.Measurable (Ioi lower) := by
  rw [ioi_eq_iUnion_naturalUpperRay]
  exact borel.iUnion fun index => measurable_ioc lower _

public theorem measurable_iic (upper : Carrier) :
    borel.Measurable (Iic upper) := by
  rw [← complement_ioi]
  exact borel.complement (measurable_ioi upper)

private noncomputable def approachBelow (boundary : Carrier) (index : Nat) : Carrier :=
  Dedekind.sub boundary
    (Dedekind.inverse
      (Dedekind.selection.ofRat (Nat.succ index : Rat)))

private theorem approachBelow_lt (boundary : Carrier) (index : Nat) :
    Dedekind.lt (approachBelow boundary index) boundary := by
  let error := Dedekind.inverse
    (Dedekind.selection.ofRat (Nat.succ index : Rat))
  have errorPositive : Dedekind.lt Dedekind.zero error :=
    Dedekind.inverse_of_positive_positive (Dedekind.ofRat_succ_positive index)
  have translated := (Dedekind.add_lt_add_left_iff
    (left := Dedekind.zero) (right := error)
    (shift := approachBelow boundary index)).mpr errorPositive
  rw [Dedekind.add_zero] at translated
  have restored :
      Dedekind.add (approachBelow boundary index) error = boundary := by
    rw [Dedekind.add_comm]
    exact Dedekind.add_sub_cancel boundary error
  rw [restored] at translated
  exact translated

private theorem iio_eq_iUnion_approachBelow (upper : Carrier) :
    Iio upper = Set.iUnion (fun index => Iic (approachBelow upper index)) := by
  apply Set.ext
  intro value
  constructor
  · intro valueLess
    have gapPositive := lt_iff_sub_positive.mp valueLess
    rcases Dedekind.exists_positive_inverse_below gapPositive with
      ⟨index, indexPositive, inverseLess⟩
    cases index with
    | zero =>
        change Dedekind.lt Dedekind.zero
          (Dedekind.selection.ofRat (0 : Rat)) at indexPositive
        rw [Dedekind.ofRat_zero] at indexPositive
        exact False.elim (Dedekind.lt_irrefl Dedekind.zero indexPositive)
    | succ predecessor =>
        refine ⟨predecessor, ?_⟩
        have shifted := (lt_sub_iff_add_lt
          (value := Dedekind.inverse
            (Dedekind.selection.ofRat (Nat.succ predecessor : Rat)))
          (upper := upper) (shift := value)).mp inverseLess
        have commuted : Dedekind.lt
            (Dedekind.add
              (Dedekind.inverse
                (Dedekind.selection.ofRat (Nat.succ predecessor : Rat)))
              value) upper := by
          rw [Dedekind.add_comm]
          exact shifted
        exact ((lt_sub_iff_add_lt
          (value := value) (upper := upper)
          (shift := Dedekind.inverse
            (Dedekind.selection.ofRat (Nat.succ predecessor : Rat)))).mpr
              commuted).left
  · rintro ⟨index, valueLe⟩
    exact Dedekind.lt_of_le_of_lt valueLe (approachBelow_lt upper index)

public theorem measurable_iio (upper : Carrier) :
    borel.Measurable (Iio upper) := by
  rw [iio_eq_iUnion_approachBelow]
  exact borel.iUnion fun index => measurable_iic (approachBelow upper index)

/-- Measurability criterion through closed lower rays.
A map into real Borel space is measurable when all closed lower ray
preimages are measurable. -/
public theorem measurableMap_borel_iff_iic {α : Type u} {source : Space α}
    {function : α → Carrier} :
    MeasurableMap source borel function ↔
      ∀ upper, source.Measurable (Set.preimage function (Iic upper)) := by
  constructor
  · intro measurable upper
    exact measurable (measurable_iic upper)
  · intro measurable
    apply MeasurableMap.into_generated
    rintro set ⟨lower, upper, rfl⟩
    rw [ioc_eq_difference]
    exact source.difference (measurable upper) (measurable lower)

/-- Measurability criterion through open lower rays.
A map into real Borel space is measurable when all open lower ray
preimages are measurable. -/
public theorem measurableMap_borel_iff_iio {α : Type u} {source : Space α}
    {function : α → Carrier} :
    MeasurableMap source borel function ↔
      ∀ upper, source.Measurable (Set.preimage function (Iio upper)) := by
  constructor
  · intro measurable upper
    exact measurable (measurable_iio upper)
  · intro measurable
    apply measurableMap_borel_iff_iic.mpr
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
        have below := Dedekind.lt_of_lt_of_le (approachBelow_lt (Dedekind.neg upper) index)
          (Dedekind.neg_le_neg_iff.mpr included)
        simpa only [Dedekind.neg_neg] using Dedekind.neg_lt_neg_iff.mpr below
      · intro bounded
        apply Classical.byContradiction
        intro missing
        have above := Dedekind.neg_lt_neg_iff.mpr (not_le_iff_lt.mp missing)
        have member : Set.iUnion (fun index => Iic
            (approachBelow (Dedekind.neg upper) index)) (Dedekind.neg (function value)) := by
          rw [← iio_eq_iUnion_approachBelow]
          exact above
        rcases member with ⟨index, included⟩
        apply (bounded index).2
        simpa only [Dedekind.neg_neg] using Dedekind.neg_le_neg_iff.mpr included
    rw [same]
    exact source.iInter fun index => measurable _

public theorem measurable_ici (lower : Carrier) :
    borel.Measurable (Ici lower) := by
  rw [← complement_iio]
  exact borel.complement (measurable_iio lower)

public theorem measurable_ioo (lower upper : Carrier) :
    borel.Measurable (Ioo lower upper) := by
  rw [ioo_eq_inter]
  exact borel.inter (measurable_ioi lower) (measurable_iio upper)

public theorem measurable_ico (lower upper : Carrier) :
    borel.Measurable (Ico lower upper) := by
  rw [ico_eq_inter]
  exact borel.inter (measurable_ici lower) (measurable_iio upper)

public theorem measurable_icc (lower upper : Carrier) :
    borel.Measurable (Icc lower upper) := by
  rw [icc_eq_inter]
  exact borel.inter (measurable_ici lower) (measurable_iic upper)

@[expose] public def IsLowerSet (set : Set Carrier) : Prop :=
  ∀ ⦃lower upper⦄, Dedekind.le lower upper → set upper → set lower

public theorem measurable_lower_set {set : Set Carrier}
    (lowerSet : IsLowerSet set) : borel.Measurable set := by
  classical
  by_cases nonempty : Set.Nonempty set
  · by_cases bounded :
        ∃ upper, Problib.Real.IsUpperBound Dedekind.le set upper
    · rcases Dedekind.exists_lub set nonempty bounded with
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
        exact measurable_iic boundary
      · have equal : set = Iio boundary := by
          apply Set.ext
          intro value
          constructor
          · intro valueMember
            have valueLe := boundaryUpper value valueMember
            refine ⟨valueLe, ?_⟩
            intro boundaryLe
            have valueEqual := Dedekind.le_antisymm valueLe boundaryLe
            exact boundaryMember (valueEqual ▸ valueMember)
          · intro valueLess
            by_cases valueMember : set value
            · exact valueMember
            · have valueUpper :
                  Problib.Real.IsUpperBound Dedekind.le set value := by
                intro candidate candidateMember
                rcases Dedekind.le_total candidate value with included | reverse
                · exact included
                · by_cases included : Dedekind.le candidate value
                  · exact included
                  · exact False.elim
                      (valueMember (lowerSet reverse candidateMember))
              exact False.elim
                (valueLess.right (boundaryLeast value valueUpper))
        rw [equal]
        exact measurable_iio boundary
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
                Problib.Real.IsUpperBound Dedekind.le set value := by
              intro candidate candidateMember
              rcases Dedekind.le_total candidate value with included | reverse
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
  apply measurableMap_borel_iff_iic.mpr
  intro upper
  let lower : Set Carrier := fun point =>
    ∃ value : α, Dedekind.le point (coordinate value) ∧
      Dedekind.le (function value) upper
  have lowerSet : IsLowerSet lower := by
    intro left right included
    rintro ⟨value, above, below⟩
    exact ⟨value, Dedekind.le_trans included above, below⟩
  have preimageEqual : Set.preimage function (Iic upper) =
      Set.preimage coordinate lower := by
    apply Set.ext
    intro value
    constructor
    · intro member
      exact ⟨value, Dedekind.le_refl _, member⟩
    · rintro ⟨other, included, bounded⟩
      exact Dedekind.le_trans (monotone included) bounded
  rw [preimageEqual]
  exact coordinateMeasurable (measurable_lower_set lowerSet)

public theorem monotone_measurable {function : Carrier → Carrier}
    (monotone : Monotone function) :
    MeasurableMap borel borel function :=
  monotone_pullback_measurable (MeasurableMap.identity borel) monotone

@[expose] public def unitSet : Set Carrier :=
  Icc Dedekind.zero Dedekind.one

public abbrev UnitInterval := { value : Carrier // unitSet value }

@[expose] public def unitZero : UnitInterval :=
  ⟨Dedekind.zero, Dedekind.le_refl _, Dedekind.one_nonnegative⟩

@[expose] public noncomputable def unitOne : UnitInterval :=
  ⟨Dedekind.one, Dedekind.one_nonnegative, Dedekind.le_refl _⟩

@[expose] public def unitInclusion (value : UnitInterval) : Carrier :=
  value.val

@[expose] public def unitBorel : Space UnitInterval :=
  Space.comap unitInclusion borel

public theorem unitInclusion_measurable :
    MeasurableMap unitBorel borel unitInclusion :=
  Space.comap_map unitInclusion borel

/-- Measurability criterion for maps into unit Borel space.
A map into `unitBorel` is measurable when preimages of open lower rays
under value inclusion are measurable. -/
public theorem measurableMap_unitBorel_iff_iio {α : Type u} {source : Space α}
    {function : α → UnitInterval} :
    MeasurableMap source unitBorel function ↔
      ∀ upper, source.Measurable (fun value => Dedekind.lt (function value).val upper) := by
  constructor
  · intro measurable upper
    exact measurable (unitInclusion_measurable (measurable_iio upper))
  · intro measurable
    have inclusion : MeasurableMap source borel (fun value => (function value).val) :=
      measurableMap_borel_iff_iio.mpr measurable
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
    exact Dedekind.le_refl Dedekind.zero
  · rw [if_neg low]
    by_cases high : Dedekind.le Dedekind.one value
    · rw [if_pos high]
      exact Dedekind.one_nonnegative
    · rw [if_neg high]
      rcases Dedekind.le_total Dedekind.zero value with included | reverse
      · exact included
      · exact False.elim (low reverse)

public theorem clampValue_le_one (value : Carrier) :
    Dedekind.le (clampValue value) Dedekind.one := by
  classical
  unfold clampValue
  by_cases low : Dedekind.le value Dedekind.zero
  · rw [if_pos low]
    exact Dedekind.one_nonnegative
  · rw [if_neg low]
    by_cases high : Dedekind.le Dedekind.one value
    · rw [if_pos high]
      exact Dedekind.le_refl Dedekind.one
    · rw [if_neg high]
      rcases Dedekind.le_total value Dedekind.one with included | reverse
      · exact included
      · exact False.elim (high reverse)

public theorem clampValue_of_mem {value : Carrier} (member : unitSet value) :
    clampValue value = value := by
  classical
  unfold unitSet at member
  unfold clampValue
  by_cases low : Dedekind.le value Dedekind.zero
  · rw [if_pos low]
    exact Dedekind.le_antisymm member.1 low
  · rw [if_neg low]
    by_cases high : Dedekind.le Dedekind.one value
    · rw [if_pos high]
      exact (Dedekind.le_antisymm member.2 high).symm
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
          leftLow (Dedekind.le_trans included rightLow)), if_pos rightHigh]]
      exact clampValue_le_one left
    · have rightNotLow : ¬Dedekind.le right Dedekind.zero := fun rightLow =>
        leftLow (Dedekind.le_trans included rightLow)
      have leftNotHigh : ¬Dedekind.le Dedekind.one left := fun leftHigh =>
        rightHigh (Dedekind.le_trans leftHigh included)
      rw [show clampValue left = left by
          unfold clampValue; rw [if_neg leftLow, if_neg leftNotHigh],
        show clampValue right = right by
          unfold clampValue; rw [if_neg rightNotLow, if_neg rightHigh]]
      exact included

public theorem clampValue_measurable :
    MeasurableMap borel borel clampValue :=
  monotone_measurable clampValue_monotone

@[expose] public noncomputable def clamp01 (value : Carrier) : UnitInterval :=
  ⟨clampValue value, clampValue_nonnegative value, clampValue_le_one value⟩

public theorem clamp01_measurable :
    MeasurableMap borel unitBorel clamp01 := by
  unfold unitBorel Space.comap
  apply MeasurableMap.into_generated
  rintro set ⟨target, targetMeasurable, rfl⟩
  exact clampValue_measurable targetMeasurable

public theorem clamp01_of_mem {value : Carrier} (member : unitSet value) :
    unitInclusion (clamp01 value) = value :=
  clampValue_of_mem member

@[expose] public def unitInitial (upper : UnitInterval) : Set UnitInterval :=
  fun value => Dedekind.le value.val upper.val

public theorem unitInitial_measurable (upper : UnitInterval) :
    unitBorel.Measurable (unitInitial upper) :=
  unitInclusion_measurable (measurable_iic upper.val)

public theorem unitInitial_one : unitInitial unitOne = Set.univ := by
  apply Set.ext
  intro value
  exact ⟨fun _ => True.intro, fun _ => value.property.2⟩

public theorem exists_unit_right_below (point : UnitInterval) (upper : Carrier)
    (room : Dedekind.lt point.val Dedekind.one)
    (below : Dedekind.lt point.val upper) :
    ∃ right : UnitInterval, Dedekind.lt point.val right.val ∧ Dedekind.lt right.val upper := by
  rcases Dedekind.le_total upper Dedekind.one with upperInside | oneBelow
  · rcases Dedekind.exists_rational_between below with ⟨rational, above, less⟩
    exact ⟨⟨Dedekind.selection.ofRat rational, Dedekind.le_trans point.property.1 above.1,
      Dedekind.le_trans less.1 upperInside⟩, above, less⟩
  · rcases Dedekind.exists_rational_between room with ⟨rational, above, less⟩
    exact ⟨⟨Dedekind.selection.ofRat rational, Dedekind.le_trans point.property.1 above.1,
      less.1⟩, above, Dedekind.lt_of_lt_of_le less oneBelow⟩

public theorem unit_monotone_measurable {function : UnitInterval → UnitInterval}
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
    apply MeasurableMap.into_generated
    rintro set ⟨target, measurable, rfl⟩
    exact ambient measurable
  have restricted : MeasurableMap unitBorel unitBorel
      (fun value => function (clamp01 (unitInclusion value))) :=
    MeasurableMap.comp extended unitInclusion_measurable
  have same : (fun value : UnitInterval =>
      function (clamp01 (unitInclusion value))) = function := by
    apply funext
    intro value
    apply congrArg function
    apply Subtype.ext
    exact clamp01_of_mem value.property
  exact same ▸ @restricted

end Problib.Measure.Real
