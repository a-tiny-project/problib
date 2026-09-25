module

public import Problib.Measure.Real.Interval
public import Problib.Real.Extended
import Std

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel,
Yury Kudryashov

Adapted from Mathlib/MeasureTheory/OuterMeasure/OfFunction.lean and
Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses ordered half-open representatives and its specialized compactness
theorem rather than topology or Mathlib's interval-cover infrastructure.
-/

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction

public section

@[expose] public noncomputable def intervalLength
    (lower upper : Carrier) : ENNReal :=
  ENNReal.ofReal (Dedekind.sub upper lower)

/-- An ordered representative of a half-open interval set. -/
public structure HalfOpenRepresentation (set : Set Carrier) where
  lower : Carrier
  upper : Carrier
  ordered : Dedekind.le lower upper
  set_eq : set = Ioc lower upper

namespace HalfOpenRepresentation

@[expose] public noncomputable def length {set : Set Carrier}
    (representation : HalfOpenRepresentation set) : ENNReal :=
  intervalLength representation.lower representation.upper

end HalfOpenRepresentation

private theorem equal_of_ordered_not_strict {left right : Carrier}
    (ordered : Dedekind.le left right) (notStrict : ¬Dedekind.lt left right) :
    left = right :=
  Dedekind.le_antisymm ordered (not_lt_iff_le.mp notStrict)

private theorem representation_length_eq {set : Set Carrier}
    (first second : HalfOpenRepresentation set) :
    first.length = second.length := by
  by_cases firstStrict : Dedekind.lt first.lower first.upper
  · have secondStrict : Dedekind.lt second.lower second.upper := by
      apply Classical.byContradiction
      intro notStrict
      have endpoints := equal_of_ordered_not_strict second.ordered notStrict
      have secondEmpty : Ioc second.lower second.upper = Set.empty := by
        rw [endpoints]
        exact ioc_empty_of_le (Dedekind.le_refl _)
      rcases ioc_nonempty firstStrict with ⟨value, member⟩
      rw [← first.set_eq, second.set_eq, secondEmpty] at member
      exact False.elim member
    have endpoints := ioc_endpoints_eq firstStrict secondStrict
      (first.set_eq.symm.trans second.set_eq)
    rw [HalfOpenRepresentation.length, HalfOpenRepresentation.length,
      endpoints.1, endpoints.2]
  · have firstEqual := equal_of_ordered_not_strict first.ordered firstStrict
    have secondStrict : ¬Dedekind.lt second.lower second.upper := by
      intro strict
      have firstEmpty : Ioc first.lower first.upper = Set.empty := by
        rw [firstEqual]
        exact ioc_empty_of_le (Dedekind.le_refl _)
      rcases ioc_nonempty strict with ⟨value, member⟩
      rw [← second.set_eq, first.set_eq, firstEmpty] at member
      exact False.elim member
    have secondEqual := equal_of_ordered_not_strict second.ordered secondStrict
    rw [HalfOpenRepresentation.length, HalfOpenRepresentation.length,
      firstEqual, secondEqual]
    unfold intervalLength
    simp only [Dedekind.sub_eq_add_neg, Dedekind.add_neg,
      ENNReal.ofReal_zero]

private noncomputable def normalizedRepresentation
    (lower upper : Carrier) : HalfOpenRepresentation (Ioc lower upper) := by
  classical
  by_cases ordered : Dedekind.le lower upper
  · exact ⟨lower, upper, ordered, rfl⟩
  · have reverse := (not_le_iff_lt.mp ordered).left
    exact ⟨Dedekind.zero, Dedekind.zero, Dedekind.le_refl _, by
      rw [ioc_empty_of_le reverse,
        ioc_empty_of_le (Dedekind.le_refl Dedekind.zero)]⟩

/-- The exact length of a half-open interval, and top for every other set. -/
@[expose] public noncomputable def intervalCost (set : Set Carrier) : ENNReal := by
  classical
  exact if represented : Nonempty (HalfOpenRepresentation set) then
    (Classical.choice represented).length
  else ENNReal.top

public theorem intervalCost_of_representation {set : Set Carrier}
    (representation : HalfOpenRepresentation set) :
    intervalCost set = representation.length := by
  classical
  unfold intervalCost
  have represented : Nonempty (HalfOpenRepresentation set) :=
    ⟨representation⟩
  simp only [dif_pos represented]
  exact representation_length_eq _ _

public theorem intervalCost_ioc (lower upper : Carrier) :
    intervalCost (Ioc lower upper) = intervalLength lower upper := by
  classical
  by_cases ordered : Dedekind.le lower upper
  · exact intervalCost_of_representation
      ⟨lower, upper, ordered, rfl⟩
  · have reverse := (not_le_iff_lt.mp ordered).left
    let zeroRepresentation : HalfOpenRepresentation (Ioc lower upper) :=
      ⟨Dedekind.zero, Dedekind.zero, Dedekind.le_refl _, by
        rw [ioc_empty_of_le reverse,
          ioc_empty_of_le (Dedekind.le_refl Dedekind.zero)]⟩
    rw [intervalCost_of_representation zeroRepresentation]
    unfold HalfOpenRepresentation.length intervalLength
    rw [Dedekind.sub_eq_add_neg, Dedekind.add_neg, ENNReal.ofReal_zero]
    symm
    apply ENNReal.ofReal_eq_zero_iff.mpr
    apply not_lt_iff_le.mp
    intro positive
    exact (not_lt_iff_le.mpr reverse) (lt_iff_sub_positive.mpr positive)

public theorem intervalCost_empty :
    intervalCost (Set.empty : Set Carrier) = ENNReal.zero := by
  rw [← ioc_empty_of_le (Dedekind.le_refl Dedekind.zero),
    intervalCost_ioc]
  unfold intervalLength
  rw [Dedekind.sub_eq_add_neg, Dedekind.add_neg, ENNReal.ofReal_zero]

@[expose] public noncomputable def splitLeftUpper
    (upper point : Carrier) : Carrier := by
  classical
  exact if Dedekind.le upper point then upper else point

@[expose] public noncomputable def splitRightLower
    (lower point : Carrier) : Carrier := by
  classical
  exact if Dedekind.le point lower then lower else point

public theorem ioc_inter_iic (lower upper point : Carrier) :
    Set.inter (Ioc lower upper) (Iic point) =
      Ioc lower (splitLeftUpper upper point) := by
  classical
  unfold splitLeftUpper
  by_cases upperPoint : Dedekind.le upper point
  · simp only [if_pos upperPoint]
    apply Set.ext
    intro value
    exact ⟨fun member => member.1,
      fun member => ⟨member, Dedekind.le_trans member.2 upperPoint⟩⟩
  · simp only [if_neg upperPoint]
    have pointUpper := not_le_iff_lt.mp upperPoint |>.left
    apply Set.ext
    intro value
    exact ⟨fun member => ⟨member.1.1, member.2⟩,
      fun member => ⟨⟨member.1,
        Dedekind.le_trans member.2 pointUpper⟩, member.2⟩⟩

public theorem ioc_inter_ioi (lower upper point : Carrier) :
    Set.inter (Ioc lower upper) (Ioi point) =
      Ioc (splitRightLower lower point) upper := by
  classical
  unfold splitRightLower
  by_cases pointLower : Dedekind.le point lower
  · simp only [if_pos pointLower]
    apply Set.ext
    intro value
    exact ⟨fun member => member.1,
      fun member => ⟨member,
        Dedekind.lt_of_le_of_lt pointLower member.1⟩⟩
  · simp only [if_neg pointLower]
    have lowerPoint := not_le_iff_lt.mp pointLower
    apply Set.ext
    intro value
    exact ⟨fun member => ⟨member.2, member.1.2⟩,
      fun member => ⟨⟨Dedekind.lt_trans lowerPoint member.1, member.2⟩,
        member.1⟩⟩

private theorem intervalLength_eq_zero_of_reverse {lower upper : Carrier}
    (reverse : Dedekind.le upper lower) :
    intervalLength lower upper = ENNReal.zero := by
  unfold intervalLength
  apply ENNReal.ofReal_eq_zero_iff.mpr
  apply not_lt_iff_le.mp
  intro positive
  exact (not_lt_iff_le.mpr reverse) (lt_iff_sub_positive.mpr positive)

private theorem split_length_interior {lower point upper : Carrier}
    (lowerPoint : Dedekind.le lower point)
    (pointUpper : Dedekind.le point upper) :
    intervalLength lower upper = ENNReal.add
      (intervalLength lower point) (intervalLength point upper) := by
  unfold intervalLength
  have firstNonnegative := Dedekind.sub_nonnegative lowerPoint
  have secondNonnegative := Dedekind.sub_nonnegative pointUpper
  rw [← ENNReal.ofReal_add firstNonnegative secondNonnegative]
  apply congrArg ENNReal.ofReal
  simp only [Dedekind.sub_eq_add_neg]
  calc
    Dedekind.sub upper lower =
        Dedekind.add upper (Dedekind.neg lower) := rfl
    _ = Dedekind.add
        (Dedekind.add point (Dedekind.neg lower))
        (Dedekind.add upper (Dedekind.neg point)) := by
      symm
      calc
        Dedekind.add
            (Dedekind.add point (Dedekind.neg lower))
            (Dedekind.add upper (Dedekind.neg point)) =
          Dedekind.add
            (Dedekind.add upper (Dedekind.neg point))
            (Dedekind.add point (Dedekind.neg lower)) :=
              Dedekind.add_comm _ _
        _ = Dedekind.add upper
            (Dedekind.add (Dedekind.neg point)
              (Dedekind.add point (Dedekind.neg lower))) :=
          Dedekind.add_assoc _ _ _
        _ = Dedekind.add upper
            (Dedekind.add
              (Dedekind.add (Dedekind.neg point) point)
              (Dedekind.neg lower)) := by
          rw [Dedekind.add_assoc]
        _ = Dedekind.add upper
            (Dedekind.add Dedekind.zero (Dedekind.neg lower)) := by
          rw [Dedekind.add_comm (Dedekind.neg point) point,
            Dedekind.add_neg]
        _ = Dedekind.add upper (Dedekind.neg lower) := by
          rw [Dedekind.add_comm Dedekind.zero, Dedekind.add_zero]

public theorem intervalLength_split (lower upper point : Carrier) :
    intervalLength lower upper = ENNReal.add
      (intervalLength lower (splitLeftUpper upper point))
      (intervalLength (splitRightLower lower point) upper) := by
  classical
  unfold splitLeftUpper splitRightLower
  by_cases upperPoint : Dedekind.le upper point
  · simp only [if_pos upperPoint]
    by_cases pointLower : Dedekind.le point lower
    · simp only [if_pos pointLower]
      rw [intervalLength_eq_zero_of_reverse
        (Dedekind.le_trans upperPoint pointLower), ENNReal.zero_add]
    · simp only [if_neg pointLower,
        intervalLength_eq_zero_of_reverse upperPoint, ENNReal.add_zero]
  · have pointUpper := not_le_iff_lt.mp upperPoint |>.left
    simp only [if_neg upperPoint]
    by_cases pointLower : Dedekind.le point lower
    · simp only [if_pos pointLower,
        intervalLength_eq_zero_of_reverse pointLower, ENNReal.zero_add]
    · simp only [if_neg pointLower]
      exact split_length_interior (not_le_iff_lt.mp pointLower).left pointUpper

public theorem intervalCost_split (lower upper point : Carrier) :
    intervalCost (Ioc lower upper) = ENNReal.add
      (intervalCost (Set.inter (Ioc lower upper) (Iic point)))
      (intervalCost (Set.inter (Ioc lower upper) (Ioi point))) := by
  rw [ioc_inter_iic, ioc_inter_ioi, intervalCost_ioc,
    intervalCost_ioc, intervalCost_ioc]
  exact intervalLength_split lower upper point

public theorem intervalCost_split_ioi (set : Set Carrier)
    (boundary : Carrier) :
    ENNReal.le
      (ENNReal.add
        (intervalCost (Set.inter set (Ioi boundary)))
        (intervalCost (Set.difference set (Ioi boundary))))
      (intervalCost set) := by
  classical
  have outside : Set.difference set (Ioi boundary) =
      Set.inter set (Iic boundary) := by
    unfold Set.difference
    rw [complement_ioi]
  rw [outside]
  by_cases represented : Nonempty (HalfOpenRepresentation set)
  · rcases represented with ⟨representation⟩
    rw [representation.set_eq, ENNReal.add_comm,
      ← intervalCost_split]
    exact ENNReal.le_refl _
  · unfold intervalCost
    simp only [dif_neg represented]
    exact ENNReal.le_top _

end

end Problib.Measure.Real
