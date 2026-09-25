module

public import Problib.Measure.Additive.AbsoluteContinuity
public import Problib.Measure.Additive.SFinite
public import Problib.Real.Series.Error

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- A finite measure with mutual absolute continuity to a target measure. -/
public structure FiniteReference (target : Measure space) : Type u where
  /-- Underlying finite measure on the ambient space. -/
  reference : Measure space
  /-- Finiteness certificate for the reference measure. -/
  finite : IsFinite reference
  /-- Target measure absolute continuity with respect to the reference. -/
  target_continuous : AbsolutelyContinuous target reference
  /-- Reference measure absolute continuity with respect to the target. -/
  reference_continuous : AbsolutelyContinuous reference target

-- Scale finite components under summable positive budgets to bound total mass.
-- Positive scaling preserves mutual null sets across countable sums.
private theorem exists_finite_reference {target : Measure space} (finite : Measure.SFinite target) :
    ∃ reference : Measure space, Measure.IsFinite reference ∧
      Measure.AbsolutelyContinuous target reference ∧
      Measure.AbsolutelyContinuous reference target := by
  classical
  rcases ENNReal.exists_positive_summable_error ENNReal.one True.intro ENNReal.one_positive with
    ⟨budgets, positive, bound⟩
  have budgetFinite : ∀ index, ENNReal.Finite (budgets index) := fun index =>
    ENNReal.finite_of_le (ENNReal.le_trans (ENNReal.term_le_tsum budgets index) bound) True.intro
  have factorsExist : ∀ index, ∃ factor, ENNReal.Finite factor ∧
      ENNReal.lt ENNReal.zero factor ∧
      ENNReal.le (ENNReal.mul factor (finite.components index Set.univ)) (budgets index) :=
    fun index => ENNReal.exists_positive_scale (finite.finite index).univ_finite
      (budgetFinite index) (positive index)
  let factors := fun index => Classical.choose (factorsExist index)
  let pieces := fun index => Measure.smul (factors index) (finite.components index)
  let reference := Measure.sum pieces
  have pieceBound : ∀ index, ENNReal.le (pieces index Set.univ) (budgets index) := by
    intro index
    change ENNReal.le ((Measure.smul (factors index) (finite.components index)) Set.univ) _
    rw [Measure.smul_apply_measurable _ _ space.univ]
    exact (Classical.choose_spec (factorsExist index)).2.2
  have referenceFinite : Measure.IsFinite reference := by
    constructor
    change ENNReal.Finite ((Measure.sum pieces) Set.univ)
    rw [Measure.sum_apply _ space.univ]
    exact ENNReal.finite_of_le (ENNReal.le_trans (ENNReal.tsum_le_tsum pieceBound) bound) True.intro
  refine ⟨reference, referenceFinite, ?_, ?_⟩
  · intro set measurable referenceZero
    have componentZero : ∀ index, finite.components index set = ENNReal.zero := by
      intro index
      have included := Measure.le_sum pieces index set
      change ENNReal.le (pieces index set) (reference set) at included
      rw [referenceZero] at included
      have scaledZero := ENNReal.eq_zero_of_le_zero included
      change (Measure.smul (factors index) (finite.components index)) set = ENNReal.zero at scaledZero
      rw [Measure.smul_apply_measurable _ _ measurable] at scaledZero
      exact (ENNReal.mul_eq_zero_iff.mp scaledZero).resolve_left
        (ENNReal.zero_lt_iff_ne_zero.mp (Classical.choose_spec (factorsExist index)).2.1)
    rw [← finite.sum_eq, Measure.sum_apply _ measurable]
    exact (ENNReal.tsum_congr componentZero).trans ENNReal.tsum_zero
  · intro set measurable targetZero
    change (Measure.sum pieces) set = ENNReal.zero
    rw [Measure.sum_apply _ measurable]
    have piecesZero : ∀ index, pieces index set = ENNReal.zero := by
      intro index
      have included := Measure.le_sum finite.components index set
      rw [finite.sum_eq, targetZero] at included
      have componentZero := ENNReal.eq_zero_of_le_zero included
      change (Measure.smul (factors index) (finite.components index)) set = ENNReal.zero
      rw [Measure.smul_apply_measurable _ _ measurable, componentZero, ENNReal.mul_zero]
    exact (ENNReal.tsum_congr piecesZero).trans ENNReal.tsum_zero

/-- Construct a finite reference measure with identical null sets for any
s-finite target measure. -/
public noncomputable def FiniteReference.ofSFinite {target : Measure space}
    (finite : SFinite target) : FiniteReference target where
  reference := Classical.choose (exists_finite_reference finite)
  finite := (Classical.choose_spec (exists_finite_reference finite)).1
  target_continuous := (Classical.choose_spec (exists_finite_reference finite)).2.1
  reference_continuous := (Classical.choose_spec (exists_finite_reference finite)).2.2

/-- The target measure and its finite reference share identical null sets for
arbitrary subsets. -/
public theorem FiniteReference.null_iff {target : Measure space}
    (reference : FiniteReference target) (set : Set alpha) :
    target.NullSet set ↔ reference.reference.NullSet set :=
  ⟨AbsolutelyContinuous.null reference.reference_continuous,
    AbsolutelyContinuous.null reference.target_continuous⟩

end Problib.Measure.Measure
