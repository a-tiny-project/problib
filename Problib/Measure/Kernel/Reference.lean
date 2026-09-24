module

public import Problib.Measure.Kernel.Scale
public import Problib.Measure.Additive.FiniteReference

set_option autoImplicit false

/-!
# Globally finite reference kernels

Constructs a globally finite transition kernel preserving fiber null sets of
an s-finite kernel. Uniform component bounds are scaled by a summable sequence of
positive weights.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- A globally finite kernel preserving the fiber null sets of a given kernel
through mutual absolute continuity. -/
public structure FiniteReference (kernel : Kernel source target) where
  reference : Kernel source target
  finite : IsFinite reference
  target_continuous : ∀ input, Measure.AbsolutelyContinuous (kernel input) (reference input)
  reference_continuous : ∀ input, Measure.AbsolutelyContinuous (reference input) (kernel input)

namespace FiniteReference

variable {kernel : Kernel source target}

/-- Fiberwise specialization of a kernel finite reference to a measure finite reference. -/
@[expose] public def fiber (reference : FiniteReference kernel) (input : α) :
    Measure.FiniteReference (kernel input) where
  reference := reference.reference input
  finite := reference.finite.measure input
  target_continuous := reference.target_continuous input
  reference_continuous := reference.reference_continuous input

/-- Constructs a globally finite reference kernel preserving fiber null sets of an
s-finite kernel. Each finite component kernel is scaled by a positive factor
ensuring a summable total mass bound. -/
public noncomputable def ofSFinite (finite : IsSFinite kernel) : FiniteReference kernel := by
  classical
  have budgetsExist := ENNReal.exists_positive_summable_error ENNReal.one True.intro ENNReal.one_positive
  let budgets := Classical.choose budgetsExist
  have positive := (Classical.choose_spec budgetsExist).1
  have sumBound := (Classical.choose_spec budgetsExist).2
  have budgetFinite : ∀ index, ENNReal.Finite (budgets index) := fun index =>
    ENNReal.finite_of_le (ENNReal.le_trans (ENNReal.term_le_tsum budgets index) sumBound) True.intro
  let bounds := fun index => Classical.choose (finite.finite index).exists_bound
  have boundProperties := fun index => Classical.choose_spec (finite.finite index).exists_bound
  have factorsExist : ∀ index, ∃ factor, ENNReal.Finite factor ∧ ENNReal.lt ENNReal.zero factor ∧
      ENNReal.le (ENNReal.mul factor (bounds index)) (budgets index) :=
    fun index => ENNReal.exists_positive_scale (boundProperties index).1 (budgetFinite index) (positive index)
  let factors := fun index => Classical.choose (factorsExist index)
  have factorProperties := fun index => Classical.choose_spec (factorsExist index)
  let pieces := fun index => Kernel.smul (factors index) (finite.components index)
  let reference := Kernel.sum pieces
  have pieceBound : ∀ index input, ENNReal.le (pieces index input Set.univ) (budgets index) := by
    intro index input
    change ENNReal.le (Measure.smul (factors index) (finite.components index input) Set.univ) _
    rw [Measure.smul_apply_measurable _ _ target.univ]
    exact ENNReal.le_trans
      (ENNReal.mul_le_mul (ENNReal.le_refl _) ((boundProperties index).2 input))
      (factorProperties index).2.2
  refine { reference := reference, finite := ?_, target_continuous := ?_, reference_continuous := ?_ }
  · refine ⟨⟨ENNReal.one, True.intro, ?_⟩⟩
    intro input
    change ENNReal.le (Measure.sum (fun index => pieces index input) Set.univ) ENNReal.one
    rw [Measure.sum_apply _ target.univ]
    exact ENNReal.le_trans (ENNReal.tsum_le_tsum (fun index => pieceBound index input)) sumBound
  · intro input set measurable referenceZero
    have componentZero : ∀ index, finite.components index input set = ENNReal.zero := by
      intro index
      have included := Measure.le_sum (fun index => pieces index input) index set
      change ENNReal.le (pieces index input set) (reference input set) at included
      rw [referenceZero] at included
      have scaledZero := ENNReal.eq_zero_of_le_zero included
      change Measure.smul (factors index) (finite.components index input) set = ENNReal.zero at scaledZero
      rw [Measure.smul_apply_measurable _ _ measurable] at scaledZero
      exact (ENNReal.mul_eq_zero_iff.mp scaledZero).resolve_left
        (ENNReal.zero_lt_iff_ne_zero.mp (factorProperties index).2.1)
    rw [← finite.sum_eq, Kernel.sum_apply, Measure.sum_apply _ measurable]
    exact (ENNReal.tsum_congr componentZero).trans ENNReal.tsum_zero
  · intro input set measurable kernelZero
    change Measure.sum (fun index => pieces index input) set = ENNReal.zero
    rw [Measure.sum_apply _ measurable]
    have piecesZero : ∀ index, pieces index input set = ENNReal.zero := by
      intro index
      have included := Measure.le_sum (fun index => finite.components index input) index set
      change ENNReal.le _ (Kernel.sum finite.components input set) at included
      rw [finite.sum_eq, kernelZero] at included
      have componentZero := ENNReal.eq_zero_of_le_zero included
      change Measure.smul (factors index) (finite.components index input) set = ENNReal.zero
      rw [Measure.smul_apply_measurable _ _ measurable, componentZero, ENNReal.mul_zero]
    exact (ENNReal.tsum_congr piecesZero).trans ENNReal.tsum_zero

end FiniteReference

end Problib.Measure.Kernel
