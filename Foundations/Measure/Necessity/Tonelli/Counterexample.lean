module

public import Foundations.Measure.Integral.Lebesgue.Algebra
public import Foundations.Measure.Kernel.Product
public import Foundations.Measure.Product
public import Foundations.Measure.Real.Lebesgue
public import Foundations.Real.Series.Basis

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

The diagonal counterexample follows the discussion in
Mathlib/MeasureTheory/Measure/Prod.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses unit-restricted Lebesgue volume and the measure that assigns infinite
mass to every nonempty Borel set.
-/

namespace Foundations.Measure.Necessity

open Foundations.Measure
open Foundations.Measure.Real
open Foundations.Real
open Foundations.Real.Construction

public section

@[expose] noncomputable def borelTopOnNonemptyValue
    (set : Set Carrier) : ENNReal := by
  classical
  exact if Set.Nonempty set then ENNReal.top else ENNReal.zero

/-- Infinite mass on every nonempty Borel set. -/
@[expose] noncomputable def topOnNonemptyBorel : Measure borel where
  content := fun set _ => borelTopOnNonemptyValue set
  empty := by
    classical
    unfold borelTopOnNonemptyValue
    rw [if_neg]
    rintro ⟨value, member⟩
    exact member
  content_iUnion_disjoint := by
    intro sets _ _
    classical
    by_cases unionNonempty : Set.Nonempty (Set.iUnion sets)
    · have unionNonemptyCopy := unionNonempty
      rcases unionNonempty with ⟨value, index, member⟩
      have indexNonempty : Set.Nonempty (sets index) := ⟨value, member⟩
      unfold borelTopOnNonemptyValue
      rw [if_pos unionNonemptyCopy]
      have term := ENNReal.termLeTsum
        (fun current =>
          if Set.Nonempty (sets current) then ENNReal.top else ENNReal.zero)
        index
      rw [if_pos indexNonempty] at term
      exact ENNReal.leAntisymm term (ENNReal.leTop _)
    · unfold borelTopOnNonemptyValue
      rw [if_neg unionNonempty]
      apply Eq.symm
      apply ENNReal.tsumEqZeroIff.mpr
      intro index
      apply if_neg
      rintro ⟨value, member⟩
      exact unionNonempty ⟨value, index, member⟩

theorem topOnNonemptyBorel_apply {set : Set Carrier}
    (setMeasurable : borel.Measurable set) :
    topOnNonemptyBorel set = borelTopOnNonemptyValue set := by
  rw [topOnNonemptyBorel, Measure.apply_measurable _ setMeasurable]

theorem topOnNonemptyBorel_singleton (point : Carrier) :
    topOnNonemptyBorel (Set.singleton point) = ENNReal.top := by
  rw [topOnNonemptyBorel_apply (measurable_singleton point)]
  unfold borelTopOnNonemptyValue
  rw [if_pos ⟨point, rfl⟩]

@[expose] noncomputable def unitVolume : Measure borel :=
  volume.restrict unitSet

theorem unitVolume_univ : unitVolume Set.univ = ENNReal.one := by
  rw [unitVolume, Measure.restrict_apply_univ, volume_Icc_zero_one]

theorem unitVolume_unitSet : unitVolume unitSet = ENNReal.one := by
  have unitMeasurable := measurable_Icc Dedekind.zero Dedekind.one
  have equal : Set.inter unitSet unitSet = unitSet := by
    apply Set.ext
    intro value
    exact ⟨fun member => member.1, fun member => ⟨member, member⟩⟩
  calc
    unitVolume unitSet = volume (Set.inter unitSet unitSet) := by
      unfold unitVolume
      exact Measure.restrict_apply volume unitSet unitMeasurable
    _ = volume unitSet := congrArg (fun set => volume set) equal
    _ = ENNReal.one := volume_Icc_zero_one

theorem unitVolume_singleton {point : Carrier} (member : unitSet point) :
    unitVolume (Set.singleton point) = ENNReal.zero := by
  rw [unitVolume,
    Measure.restrict_apply volume unitSet (measurable_singleton point)]
  have equal : Set.inter (Set.singleton point) unitSet =
      Set.singleton point := by
    apply Set.ext
    intro value
    constructor
    · exact fun present => present.1
    · intro equal
      subst value
      exact ⟨rfl, member⟩
  rw [equal, volume_singleton]

private noncomputable def rationalPoint (index : Nat) : Carrier :=
  ENNReal.toReal (ENNReal.rationalBasis index)

private def orderedUnitPair : Set (Carrier × Carrier) :=
  fun value => unitSet value.1 ∧ unitSet value.2 ∧
    Dedekind.lt value.1 value.2

private noncomputable def rationalRectangle
    (index : Nat) : Set (Carrier × Carrier) :=
  Set.product
    (Set.inter unitSet (Iio (rationalPoint index)))
    (Set.inter unitSet (Ioi (rationalPoint index)))

private theorem rationalRectangle_measurable (index : Nat) :
    (Space.product borel borel).Measurable (rationalRectangle index) :=
  Space.product_set_measurable borel borel
    (borel.inter (measurable_Icc Dedekind.zero Dedekind.one)
      (measurable_Iio (rationalPoint index)))
    (borel.inter (measurable_Icc Dedekind.zero Dedekind.one)
      (measurable_Ioi (rationalPoint index)))

private theorem orderedUnitPair_eq_iUnion :
    orderedUnitPair = Set.iUnion rationalRectangle := by
  apply Set.ext
  intro value
  constructor
  · intro member
    have less : ENNReal.lt (ENNReal.ofReal value.1)
        (ENNReal.ofReal value.2) :=
      (ENNReal.ofRealLtOfRealIff member.1.1 member.2.1.1).mpr member.2.2
    rcases ENNReal.existsRationalBasisBetween less with
      ⟨index, leftLess, rightLess⟩
    have leftLessReal : Dedekind.lt value.1 (rationalPoint index) := by
      have converted := (ENNReal.toRealLtToRealIff
        (ENNReal.ofRealFinite value.1)
        (ENNReal.rationalBasisFinite index)).mpr leftLess
      rw [ENNReal.toRealOfReal member.1.1] at converted
      exact converted
    have rightLessReal : Dedekind.lt (rationalPoint index) value.2 := by
      have converted := (ENNReal.toRealLtToRealIff
        (ENNReal.rationalBasisFinite index)
        (ENNReal.ofRealFinite value.2)).mpr rightLess
      rw [ENNReal.toRealOfReal member.2.1.1] at converted
      exact converted
    exact ⟨index, ⟨member.1, leftLessReal⟩,
      ⟨member.2.1, rightLessReal⟩⟩
  · rintro ⟨index, leftMember, rightMember⟩
    exact ⟨leftMember.1, rightMember.1,
      ltTrans leftMember.2 rightMember.2⟩

private theorem orderedUnitPair_measurable :
    (Space.product borel borel).Measurable orderedUnitPair := by
  rw [orderedUnitPair_eq_iUnion]
  exact (Space.product borel borel).iUnion rationalRectangle_measurable

private def unitPair : Set (Carrier × Carrier) :=
  Set.product unitSet unitSet

private def offDiagonal : Set (Carrier × Carrier) :=
  Set.union orderedUnitPair
    (Set.preimage (fun value => (value.2, value.1)) orderedUnitPair)

/-- The diagonal restricted to the closed unit square. -/
@[expose] def restrictedDiagonal : Set (Carrier × Carrier) :=
  fun value => unitSet value.1 ∧ unitSet value.2 ∧ value.1 = value.2

private theorem restrictedDiagonal_eq_difference :
    restrictedDiagonal = Set.difference unitPair offDiagonal := by
  apply Set.ext
  intro value
  constructor
  · intro member
    refine ⟨⟨member.1, member.2.1⟩, ?_⟩
    intro off
    rcases off with forward | reverse
    · unfold orderedUnitPair at forward
      exact Dedekind.ltIrrefl value.2 (member.2.2 ▸ forward.2.2)
    · unfold Set.preimage orderedUnitPair at reverse
      have reverseLess : Dedekind.lt value.2 value.1 := reverse.2.2
      rw [member.2.2] at reverseLess
      exact Dedekind.ltIrrefl value.2 reverseLess
  · intro member
    refine ⟨member.1.1, member.1.2, ?_⟩
    apply Dedekind.leAntisymm
    · apply Classical.byContradiction
      intro notIncluded
      exact member.2 (Or.inr ⟨member.1.2, member.1.1,
        notLeIffLt.mp notIncluded⟩)
    · apply Classical.byContradiction
      intro notIncluded
      exact member.2 (Or.inl ⟨member.1.1, member.1.2,
        notLeIffLt.mp notIncluded⟩)

theorem restrictedDiagonal_measurable :
    (Space.product borel borel).Measurable restrictedDiagonal := by
  rw [restrictedDiagonal_eq_difference]
  apply (Space.product borel borel).difference
  · exact Space.product_set_measurable borel borel
      (measurable_Icc Dedekind.zero Dedekind.one)
      (measurable_Icc Dedekind.zero Dedekind.one)
  · exact (Space.product borel borel).union orderedUnitPair_measurable
      (Space.swap_measurable borel borel orderedUnitPair_measurable)

@[expose] noncomputable def restrictedDiagonalIndicator :
    Carrier × Carrier → ENNReal :=
  ennrealIndicator restrictedDiagonal (fun _ => ENNReal.one)

theorem restrictedDiagonalIndicator_measurable :
    ENNRealMeasurable (Space.product borel borel)
      restrictedDiagonalIndicator :=
  ENNRealMeasurable.indicator restrictedDiagonal_measurable
    (ENNRealMeasurable.constant _ ENNReal.one)

private theorem diagonal_left_of_mem {point : Carrier}
    (member : unitSet point) :
    (fun value => restrictedDiagonalIndicator (point, value)) =
      ennrealIndicator (Set.singleton point) (fun _ => ENNReal.one) := by
  funext value
  classical
  unfold restrictedDiagonalIndicator restrictedDiagonal
  unfold ennrealIndicator ennrealPiecewise Set.singleton
  by_cases equal : value = point
  · subst value
    simp [member]
  · have reverse : point ≠ value := fun same => equal same.symm
    simp [equal, reverse]

private theorem diagonal_left_of_not_mem {point : Carrier}
    (notMember : ¬unitSet point) :
    (fun value => restrictedDiagonalIndicator (point, value)) =
      (fun _ => ENNReal.zero) := by
  funext value
  simp [restrictedDiagonalIndicator, restrictedDiagonal,
    ennrealIndicator, ennrealPiecewise, notMember]

private theorem diagonal_right_of_mem {point : Carrier}
    (member : unitSet point) :
    (fun value => restrictedDiagonalIndicator (value, point)) =
      ennrealIndicator (Set.singleton point) (fun _ => ENNReal.one) := by
  funext value
  classical
  unfold restrictedDiagonalIndicator restrictedDiagonal
  unfold ennrealIndicator ennrealPiecewise Set.singleton
  by_cases equal : value = point
  · subst value
    simp [member]
  · simp [equal]

private theorem diagonal_right_of_not_mem {point : Carrier}
    (notMember : ¬unitSet point) :
    (fun value => restrictedDiagonalIndicator (value, point)) =
      (fun _ => ENNReal.zero) := by
  funext value
  simp [restrictedDiagonalIndicator, restrictedDiagonal,
    ennrealIndicator, ennrealPiecewise, notMember]

theorem diagonal_inner_top (point : Carrier) :
    lintegral topOnNonemptyBorel
        (fun value => restrictedDiagonalIndicator (point, value)) =
      ennrealIndicator unitSet (fun _ => ENNReal.top) point := by
  classical
  by_cases member : unitSet point
  · rw [diagonal_left_of_mem member,
      lintegral_indicator topOnNonemptyBorel (Set.singleton point)
        (measurable_singleton point),
      lintegral_const, Measure.restrict_apply_univ,
      topOnNonemptyBorel_singleton, ENNReal.oneMul]
    simp [ennrealIndicator, ennrealPiecewise, member]
  · rw [diagonal_left_of_not_mem member, lintegral_zero]
    simp [ennrealIndicator, ennrealPiecewise, member]

theorem diagonal_inner_zero (point : Carrier) :
    lintegral unitVolume
        (fun value => restrictedDiagonalIndicator (value, point)) =
      ENNReal.zero := by
  classical
  by_cases member : unitSet point
  · rw [diagonal_right_of_mem member,
      lintegral_indicator unitVolume (Set.singleton point)
        (measurable_singleton point),
      lintegral_const, Measure.restrict_apply_univ,
      unitVolume_singleton member, ENNReal.mulZero]
  · rw [diagonal_right_of_not_mem member, lintegral_zero]

theorem diagonal_iterated_top :
    lintegral unitVolume (fun first =>
      lintegral topOnNonemptyBorel (fun second =>
        restrictedDiagonalIndicator (first, second))) = ENNReal.top := by
  have equal : (fun first => lintegral topOnNonemptyBorel (fun second =>
      restrictedDiagonalIndicator (first, second))) =
      ennrealIndicator unitSet (fun _ => ENNReal.top) := by
    funext first
    exact diagonal_inner_top first
  rw [equal, lintegral_indicator unitVolume unitSet
    (measurable_Icc Dedekind.zero Dedekind.one),
    lintegral_const, Measure.restrict_apply_univ,
    unitVolume_unitSet, ENNReal.mulOne]

theorem diagonal_iterated_zero :
    lintegral topOnNonemptyBorel (fun second =>
      lintegral unitVolume (fun first =>
        restrictedDiagonalIndicator (first, second))) = ENNReal.zero := by
  have equal : (fun second => lintegral unitVolume (fun first =>
      restrictedDiagonalIndicator (first, second))) =
      (fun _ => ENNReal.zero) := by
    funext second
    exact diagonal_inner_zero second
  rw [equal, lintegral_zero]

theorem diagonal_iterated_ne :
    lintegral unitVolume (fun first =>
      lintegral topOnNonemptyBorel (fun second =>
        restrictedDiagonalIndicator (first, second))) ≠
    lintegral topOnNonemptyBorel (fun second =>
      lintegral unitVolume (fun first =>
        restrictedDiagonalIndicator (first, second))) := by
  rw [diagonal_iterated_top, diagonal_iterated_zero]
  exact ENNReal.topNeFinite NNReal.zero

theorem topOnNonemptyBorel_not_sFinite :
    Measure.SFinite topOnNonemptyBorel → False := by
  intro infiniteFinite
  let unitFinite : Measure.IsFinite unitVolume := ⟨by
    rw [unitVolume_univ]
    exact True.intro⟩
  let unitSFinite := Measure.SFinite.ofFinite unitFinite
  have forward := lintegral_prod unitVolume topOnNonemptyBorel
    infiniteFinite restrictedDiagonalIndicator_measurable
  have reverse := lintegral_prod_symm unitVolume topOnNonemptyBorel
    unitSFinite infiniteFinite restrictedDiagonalIndicator_measurable
  exact diagonal_iterated_ne (forward.symm.trans reverse)

/-- Without s-finiteness, the two Tonelli iterates can disagree. -/
theorem tonelli_fails_without_sFinite :
    (Measure.SFinite topOnNonemptyBorel → False) ∧
      lintegral unitVolume (fun first =>
        lintegral topOnNonemptyBorel (fun second =>
          restrictedDiagonalIndicator (first, second))) ≠
      lintegral topOnNonemptyBorel (fun second =>
        lintegral unitVolume (fun first =>
          restrictedDiagonalIndicator (first, second))) :=
  ⟨topOnNonemptyBorel_not_sFinite, diagonal_iterated_ne⟩

end

end Foundations.Measure.Necessity
