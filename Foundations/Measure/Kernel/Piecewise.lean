module

public import Foundations.Measure.Kernel.Basic

set_option autoImplicit false

namespace Foundations.Measure.Kernel

open Foundations.Real

universe u v
variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Construct a measurable kernel by branching on a measurable source set. -/
@[expose] public noncomputable def piecewise (region : Set α) (measurable : source.Measurable region)
    (left right : Kernel source target) : Kernel source target := by
  classical
  refine {
    toFun := fun input => if region input then left input else right input
    measurable := ?_
  }
  intro set setMeasurable
  have equal : (fun input => (if region input then left input else right input) set) =
      ennrealPiecewise region (fun input => left input set) (fun input => right input set) := by
    funext input
    by_cases member : region input
    · simp only [if_pos member, ennrealPiecewise]
    · simp only [if_neg member, ennrealPiecewise]
  rw [equal]
  exact ENNRealMeasurable.piecewise measurable
    (left.measurable setMeasurable) (right.measurable setMeasurable)

/-- Evaluate a piecewise kernel at an input in the active region. -/
@[simp] public theorem piecewise_apply_of_mem
    (region : Set α) (measurable : source.Measurable region)
    (left right : Kernel source target) (input : α) (member : region input) :
    piecewise region measurable left right input = left input := by
  classical
  change (if region input then left input else right input) = left input
  rw [if_pos member]

/-- Evaluate a piecewise kernel at an input outside the active region. -/
@[simp] public theorem piecewise_apply_of_not_mem
    (region : Set α) (measurable : source.Measurable region)
    (left right : Kernel source target) (input : α) (outside : ¬region input) :
    piecewise region measurable left right input = right input := by
  classical
  change (if region input then left input else right input) = right input
  rw [if_neg outside]

/-- Distribute countable summation across both branches of a piecewise
kernel. -/
public theorem piecewise_sum
    (region : Set α) (measurable : source.Measurable region)
    (left right : Nat → Kernel source target) :
    piecewise region measurable (Kernel.sum left) (Kernel.sum right) =
      Kernel.sum (fun index => piecewise region measurable (left index) (right index)) := by
  classical
  apply Kernel.ext
  intro input
  by_cases member : region input
  · rw [piecewise_apply_of_mem _ _ _ _ _ member]
    simp only [Kernel.sum_apply]
    apply congrArg Measure.sum
    funext index
    exact (piecewise_apply_of_mem _ _ _ _ _ member).symm
  · rw [piecewise_apply_of_not_mem _ _ _ _ _ member]
    simp only [Kernel.sum_apply]
    apply congrArg Measure.sum
    funext index
    exact (piecewise_apply_of_not_mem _ _ _ _ _ member).symm

/-- Prove that piecewise selection between uniformly finite kernels remains
uniformly finite. -/
public theorem IsFinite.piecewise {left right : Kernel source target}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    (region : Set α) (measurable : source.Measurable region) :
    IsFinite (Kernel.piecewise region measurable left right) := by
  classical
  rcases leftFinite.exists_bound with ⟨leftBound, leftBoundFinite, leftBounded⟩
  rcases rightFinite.exists_bound with ⟨rightBound, rightBoundFinite, rightBounded⟩
  refine ⟨⟨ENNReal.add leftBound rightBound,
    ENNReal.addFinite leftBoundFinite rightBoundFinite, ?_⟩⟩
  intro input
  by_cases member : region input
  · rw [piecewise_apply_of_mem _ _ _ _ _ member]
    apply ENNReal.leTrans (leftBounded input)
    simpa only [ENNReal.addZero] using
      ENNReal.addLeAddLeft (ENNReal.zeroLe rightBound) leftBound
  · rw [piecewise_apply_of_not_mem _ _ _ _ _ member]
    apply ENNReal.leTrans (rightBounded input)
    simpa only [ENNReal.zeroAdd] using
      ENNReal.addLeAddRight (ENNReal.zeroLe leftBound) rightBound

/-- Construct an s-finite certificate for a piecewise kernel from s-finite
branches. -/
public noncomputable def IsSFinite.piecewise {left right : Kernel source target}
    (leftFinite : IsSFinite left) (rightFinite : IsSFinite right)
    (region : Set α) (measurable : source.Measurable region) :
    IsSFinite (Kernel.piecewise region measurable left right) where
  components := fun index => Kernel.piecewise region measurable
    (leftFinite.components index) (rightFinite.components index)
  finite := fun index => (leftFinite.finite index).piecewise
    (rightFinite.finite index) region measurable
  sum_eq := by
    rw [← piecewise_sum, leftFinite.sum_eq, rightFinite.sum_eq]

end Foundations.Measure.Kernel
