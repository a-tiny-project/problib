module

public import Foundations.Measure.Extended.Basic
public import Foundations.Real.Series.Basis

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kexing Ying

Adapted from Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean at
commit 15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny obtains lower rays and comparisons from the countable nonnegative
rational basis, without a topology or a typeclass hierarchy.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

private theorem notLtIffLe (left right : ENNReal) :
    (¬ENNReal.lt left right) ↔ ENNReal.le right left := by
  constructor
  · intro notLess
    rcases ENNReal.leTotal right left with reverse | forward
    · exact reverse
    · apply Classical.byContradiction
      intro notReverse
      exact notLess ⟨forward, notReverse⟩
  · intro reverse less
    exact less.right reverse

private theorem notLeIffLt (left right : ENNReal) :
    (¬ENNReal.le left right) ↔ ENNReal.lt right left := by
  constructor
  · intro notIncluded
    refine ⟨?_, notIncluded⟩
    exact Or.resolve_left (ENNReal.leTotal left right) notIncluded
  · intro less included
    exact less.right included

namespace ENNRealMeasurable

variable {α : Type u} {source : Space α}
  {function left right : α → ENNReal}

public theorem iic (measurable : ENNRealMeasurable source function)
    (threshold : ENNReal) :
    source.Measurable (Set.preimage function (ennrealIic threshold)) := by
  have complementMeasurable := source.complement (measurable threshold)
  have equal : Set.preimage function (ennrealIic threshold) =
      Set.complement
        (Set.preimage function (ennrealIoi threshold)) := by
    apply Set.ext
    intro value
    change ENNReal.le (function value) threshold ↔
      ¬ENNReal.lt threshold (function value)
    exact Iff.symm (notLtIffLe threshold (function value))
  rw [equal]
  exact complementMeasurable

public theorem iio (measurable : ENNRealMeasurable source function)
    (threshold : ENNReal) :
    source.Measurable (Set.preimage function (ennrealIio threshold)) := by
  classical
  let sets : Nat → Set α := fun index =>
    if ENNReal.lt (ENNReal.rationalBasis index) threshold then
      Set.preimage function (ennrealIic (ENNReal.rationalBasis index))
    else Set.empty
  have setsMeasurable : ∀ index, source.Measurable (sets index) := by
    intro index
    by_cases below : ENNReal.lt (ENNReal.rationalBasis index) threshold
    · simp only [sets, if_pos below]
      exact iic measurable (ENNReal.rationalBasis index)
    · simp only [sets, if_neg below]
      exact source.empty
  have equal : Set.preimage function (ennrealIio threshold) =
      Set.iUnion sets := by
    apply Set.ext
    intro value
    constructor
    · intro less
      rcases ENNReal.existsRationalBasisBetween less with
        ⟨index, valueBasis, basisThreshold⟩
      refine ⟨index, ?_⟩
      simp only [sets, if_pos basisThreshold]
      exact valueBasis.left
    · rintro ⟨index, member⟩
      by_cases below : ENNReal.lt (ENNReal.rationalBasis index) threshold
      · simp only [sets, if_pos below] at member
        refine ⟨ENNReal.leTrans member below.left, ?_⟩
        intro thresholdValue
        exact below.right (ENNReal.leTrans thresholdValue member)
      · simp only [sets, if_neg below] at member
        exact False.elim member
  rw [equal]
  exact source.iUnion setsMeasurable

public theorem ici (measurable : ENNRealMeasurable source function)
    (threshold : ENNReal) :
    source.Measurable (Set.preimage function (ennrealIci threshold)) := by
  have complementMeasurable := source.complement (iio measurable threshold)
  have equal : Set.preimage function (ennrealIci threshold) =
      Set.complement
        (Set.preimage function (ennrealIio threshold)) := by
    apply Set.ext
    intro value
    change ENNReal.le threshold (function value) ↔
      ¬ENNReal.lt (function value) threshold
    exact Iff.symm (notLtIffLe (function value) threshold)
  rw [equal]
  exact complementMeasurable

public theorem singleton (measurable : ENNRealMeasurable source function)
    (target : ENNReal) :
    source.Measurable
      (Set.preimage function (ennrealSingleton target)) := by
  have intersection := source.inter (iic measurable target)
    (ici measurable target)
  have equal : Set.preimage function (ennrealSingleton target) =
      Set.inter (Set.preimage function (ennrealIic target))
        (Set.preimage function (ennrealIci target)) := by
    apply Set.ext
    intro value
    change function value = target ↔
      ENNReal.le (function value) target ∧
        ENNReal.le target (function value)
    constructor
    · intro equal
      rw [equal]
      exact ⟨ENNReal.leRefl target, ENNReal.leRefl target⟩
    · intro both
      exact ENNReal.leAntisymm both.1 both.2
  rw [equal]
  exact intersection

public theorem lt_set (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right) :
    source.Measurable
      (fun value => ENNReal.lt (left value) (right value)) := by
  let sets : Nat → Set α := fun index =>
    Set.inter
      (Set.preimage left (ennrealIic (ENNReal.rationalBasis index)))
      (Set.preimage right (ennrealIoi (ENNReal.rationalBasis index)))
  have setsMeasurable : ∀ index, source.Measurable (sets index) := by
    intro index
    exact source.inter
      (iic leftMeasurable (ENNReal.rationalBasis index))
      (rightMeasurable (ENNReal.rationalBasis index))
  have equal : (fun value => ENNReal.lt (left value) (right value)) =
      Set.iUnion sets := by
    apply Set.ext
    intro value
    constructor
    · intro less
      rcases ENNReal.existsRationalBasisBetween less with
        ⟨index, leftBasis, basisRight⟩
      exact ⟨index, leftBasis.left, basisRight⟩
    · rintro ⟨index, leftBasis, basisRight⟩
      refine ⟨ENNReal.leTrans leftBasis basisRight.left, ?_⟩
      intro rightLeft
      exact basisRight.right (ENNReal.leTrans rightLeft leftBasis)
  rw [equal]
  exact source.iUnion setsMeasurable

public theorem le_set (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right) :
    source.Measurable
      (fun value => ENNReal.le (left value) (right value)) := by
  have complementMeasurable := source.complement
    (lt_set rightMeasurable leftMeasurable)
  have equal : (fun value => ENNReal.le (left value) (right value)) =
      Set.complement
        (fun value => ENNReal.lt (right value) (left value)) := by
    apply Set.ext
    intro value
    exact Iff.symm (notLtIffLe (right value) (left value))
  rw [equal]
  exact complementMeasurable

public theorem eq_set (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right) :
    source.Measurable (fun value => left value = right value) := by
  have intersection := source.inter
    (le_set leftMeasurable rightMeasurable)
    (le_set rightMeasurable leftMeasurable)
  have equal : (fun value => left value = right value) =
      Set.inter (fun value => ENNReal.le (left value) (right value))
        (fun value => ENNReal.le (right value) (left value)) := by
    apply Set.ext
    intro value
    change (left value = right value) ↔
      ENNReal.le (left value) (right value) ∧
        ENNReal.le (right value) (left value)
    constructor
    · intro same
      rw [same]
      exact ⟨ENNReal.leRefl _, ENNReal.leRefl _⟩
    · intro both
      exact ENNReal.leAntisymm both.1 both.2
  rw [equal]
  exact intersection

public theorem approximation
    (measurable : ENNRealMeasurable source function) (index : Nat) :
    ENNRealMeasurable source
      (fun value => ENNReal.approximation (function value) index) := by
  induction index with
  | zero =>
      have equal : (fun value : α =>
          ENNReal.approximation (function value) 0) =
          (fun _ => ENNReal.zero) := by
        funext value
        rfl
      rw [equal]
      exact constant source ENNReal.zero
  | succ index induction =>
      let included : Set α := fun value =>
        ENNReal.le (ENNReal.rationalBasis index) (function value)
      let dominates : Set α := fun value =>
        ENNReal.le (ENNReal.approximation (function value) index)
          (ENNReal.rationalBasis index)
      have includedMeasurable : source.Measurable included :=
        ici measurable (ENNReal.rationalBasis index)
      have dominatesMeasurable : source.Measurable dominates :=
        iic induction (ENNReal.rationalBasis index)
      have inner := piecewise dominatesMeasurable
        (constant source (ENNReal.rationalBasis index)) induction
      have outer := piecewise includedMeasurable inner induction
      have equal : (fun value : α =>
          ENNReal.approximation (function value) (index + 1)) =
          ennrealPiecewise included
            (ennrealPiecewise dominates
              (fun _ => ENNReal.rationalBasis index)
              (fun value => ENNReal.approximation (function value) index))
            (fun value => ENNReal.approximation (function value) index) := by
        classical
        funext value
        by_cases valueIncluded :
            ENNReal.le (ENNReal.rationalBasis index) (function value)
        · by_cases valueDominates :
              ENNReal.le (ENNReal.approximation (function value) index)
                (ENNReal.rationalBasis index)
          · simp [ENNReal.approximation, ennrealPiecewise, included,
              dominates, valueIncluded, valueDominates]
          · simp [ENNReal.approximation, ennrealPiecewise, included,
              dominates, valueIncluded, valueDominates]
        · simp [ENNReal.approximation, ennrealPiecewise, included,
            valueIncluded]
      rw [equal]
      exact outer

public theorem iSup {functions : Nat → α → ENNReal}
    (measurable : ∀ index,
      ENNRealMeasurable source (functions index)) :
    ENNRealMeasurable source
      (fun value => ENNReal.iSup (fun index => functions index value)) := by
  intro threshold
  have unionMeasurable := source.iUnion fun index =>
    measurable index threshold
  have equal : Set.preimage
      (fun value => ENNReal.iSup (fun index => functions index value))
        (ennrealIoi threshold) =
      Set.iUnion (fun index =>
        Set.preimage (functions index) (ennrealIoi threshold)) := by
    apply Set.ext
    intro value
    constructor
    · intro less
      exact ENNReal.existsIndexGreaterOfLtISup less
    · rintro ⟨index, less⟩
      refine ⟨ENNReal.leTrans less.left
          (ENNReal.leISup (fun position => functions position value) index), ?_⟩
      intro supremumThreshold
      exact less.right (ENNReal.leTrans
        (ENNReal.leISup (fun position => functions position value) index)
        supremumThreshold)
  rw [equal]
  exact unionMeasurable

/-- Pointwise infima of countable families of extended-nonnegative measurable
functions are measurable without monotonicity hypotheses. -/
public theorem iInf {functions : Nat → α → ENNReal}
    (measurable : ∀ index, ENNRealMeasurable source (functions index)) :
    ENNRealMeasurable source (fun input => ENNReal.iInf (fun index => functions index input)) := by
  intro threshold
  let regions := fun index => fun input =>
    ENNReal.lt threshold (ENNReal.rationalBasis index) ∧
      ∀ stage, ENNReal.le (ENNReal.rationalBasis index) (functions stage input)
  have regionsMeasurable : ∀ index, source.Measurable (regions index) := by
    intro index
    classical
    by_cases below : ENNReal.lt threshold (ENNReal.rationalBasis index)
    · have same : regions index = Set.iInter (fun stage =>
          Set.preimage (functions stage) (ennrealIci (ENNReal.rationalBasis index))) :=
        Set.ext fun _ => ⟨fun both => both.2, fun all => ⟨below, all⟩⟩
      rw [same]
      exact source.iInter (fun stage => (measurable stage).ici _)
    · have same : regions index = Set.empty :=
        Set.ext fun _ => ⟨fun both => below both.1, False.elim⟩
      rw [same]
      exact source.empty
  have same : Set.preimage (fun input => ENNReal.iInf (fun index => functions index input))
      (ennrealIoi threshold) = Set.iUnion regions := by
    apply Set.ext
    intro input
    constructor
    · intro less
      rcases ENNReal.existsRationalBasisBetween less with ⟨index, above, below⟩
      exact ⟨index, above, fun stage => ENNReal.leTrans below.1 (ENNReal.iInfLe _ stage)⟩
    · rintro ⟨index, above, below⟩
      have bound := ENNReal.leIInf below
      exact ⟨ENNReal.leTrans above.1 bound, fun reverse => above.2 (ENNReal.leTrans bound reverse)⟩
  rw [same]
  exact source.iUnion regionsMeasurable

public structure IsMonotoneLimit (functions : Nat → α → ENNReal)
    (limit : α → ENNReal) : Prop where
  monotone : ∀ value first second, first ≤ second →
    ENNReal.le (functions first value) (functions second value)
  supremum : ∀ value,
    limit value = ENNReal.iSup (fun index => functions index value)

public theorem monotoneLimit {functions : Nat → α → ENNReal}
    {limit : α → ENNReal}
    (measurable : ∀ index,
      ENNRealMeasurable source (functions index))
    (converges : IsMonotoneLimit functions limit) :
    ENNRealMeasurable source limit := by
  have supremumMeasurable := iSup measurable
  have equal : limit = fun value =>
      ENNReal.iSup (fun index => functions index value) := by
    funext value
    exact converges.supremum value
  rw [equal]
  exact supremumMeasurable

/-- Pointwise maximum of two measurable extended nonnegative real functions is
measurable. -/
public theorem max {left right : α → ENNReal}
    (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right) :
    ENNRealMeasurable source (fun value => ENNReal.max (left value) (right value)) := by
  have measurable := piecewise (le_set leftMeasurable rightMeasurable)
    rightMeasurable leftMeasurable
  have equal : (fun value => ENNReal.max (left value) (right value)) =
      ennrealPiecewise (fun value => ENNReal.le (left value) (right value)) right left := by
    funext value
    classical
    by_cases included : ENNReal.le (left value) (right value)
    · rw [ENNReal.maxEqRight included]
      simp only [ennrealPiecewise, if_pos included]
    · rw [ENNReal.maxEqLeft ((ENNReal.leTotal _ _).resolve_left included)]
      simp only [ennrealPiecewise, if_neg included]
  rw [equal]
  exact measurable

end ENNRealMeasurable

end Foundations.Measure
