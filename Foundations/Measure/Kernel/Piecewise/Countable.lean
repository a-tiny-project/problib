module

public import Foundations.Measure.Kernel.Piecewise

set_option autoImplicit false

/-!
# Countable piecewise branch selection for transition kernels

Constructs transition kernels by selecting among a sequence of branch kernels
along a countable measurable partition. Proves decomposition as a sum of
zeroed branches, uniform finiteness under a common bound, and s-finiteness.
-/
namespace Foundations.Measure.Kernel

open Foundations.Real

public section

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Assemble a transition kernel from a countable sequence of branch kernels
along a measurable partition. -/
@[expose] noncomputable def countablePiecewise (partition : α → Nat)
    (measurable : ∀ index, source.Measurable (fun input => partition input = index))
    (kernels : Nat → Kernel source target) : Kernel source target where
  toFun := fun input => kernels (partition input) input
  measurable := fun regionMeasurable =>
    ENNRealMeasurable.ofMeasurableMap (MeasurableMap.countablePiecewise measurable
      (fun index => ((kernels index).measurable regionMeasurable).measurableMap))

/-- Evaluate a countable piecewise transition kernel at an input point. -/
@[simp] theorem countablePiecewise_apply (partition : α → Nat)
    (measurable : ∀ index, source.Measurable (fun input => partition input = index))
    (kernels : Nat → Kernel source target) (input : α) :
    countablePiecewise partition measurable kernels input = kernels (partition input) input := rfl

/-- Countable piecewise branch selection distributes over countable sums of
branch kernels. -/
theorem countablePiecewise_sum (partition : α → Nat)
    (measurable : ∀ index, source.Measurable (fun input => partition input = index))
    (kernels : Nat → Nat → Kernel source target) :
    countablePiecewise partition measurable (fun branch => Kernel.sum (kernels branch)) =
      Kernel.sum (fun index =>
        countablePiecewise partition measurable (fun branch => kernels branch index)) := by
  apply Kernel.ext
  intro input
  rfl

/-- Express a countable piecewise kernel as a countable sum of branches zeroed
outside their respective partition cells. -/
theorem countablePiecewise_eq_sum_piecewise (partition : α → Nat)
    (measurable : ∀ index, source.Measurable (fun input => partition input = index))
    (kernels : Nat → Kernel source target) :
    countablePiecewise partition measurable kernels =
      Kernel.sum (fun index => piecewise (fun input => partition input = index)
        (measurable index) (kernels index) (Kernel.zero source target)) := by
  apply Kernel.ext_measurable
  intro input region regionMeasurable
  rw [Kernel.sum_apply, Measure.sum_apply _ regionMeasurable, countablePiecewise_apply]
  symm
  calc
    ENNReal.tsum (fun index =>
        piecewise (fun input => partition input = index) (measurable index)
          (kernels index) (Kernel.zero source target) input region) =
        ENNReal.tsum (ENNReal.single (partition input) (kernels (partition input) input region)) := by
      apply ENNReal.tsumCongr
      intro index
      by_cases equal : index = partition input
      · subst index
        rw [piecewise_apply_of_mem (fun value => partition value = partition input)
          (measurable (partition input)) (kernels (partition input))
          (Kernel.zero source target) input rfl]
        simp only [ENNReal.single, ↓reduceIte]
      · rw [piecewise_apply_of_not_mem (fun value => partition value = index)
          (measurable index) (kernels index) (Kernel.zero source target) input (Ne.symm equal), Kernel.zero_apply,
          Measure.zero_apply]
        simp only [ENNReal.single, equal, ↓reduceIte]
    _ = kernels (partition input) input region := ENNReal.tsumSingle _ _

/-- Countable piecewise selection preserves uniform finiteness when one common
finite bound bounds all branch kernels. -/
theorem IsFinite.countablePiecewise (partition : α → Nat)
    (measurable : ∀ index, source.Measurable (fun input => partition input = index))
    (kernels : Nat → Kernel source target) (bound : ENNReal) (boundFinite : bound.Finite)
    (bounded : ∀ index input, ENNReal.le (kernels index input Set.univ) bound) :
    IsFinite (Kernel.countablePiecewise partition measurable kernels) :=
  ⟨⟨bound, boundFinite, fun input => bounded (partition input) input⟩⟩

/-- Countable piecewise selection preserves s-finiteness by zeroing branch
s-finite certificates and summing them without a common bound. -/
noncomputable def IsSFinite.countablePiecewise (partition : α → Nat)
    (measurable : ∀ index, source.Measurable (fun input => partition input = index))
    (kernels : Nat → Kernel source target) (finite : ∀ index, IsSFinite (kernels index)) :
    IsSFinite (Kernel.countablePiecewise partition measurable kernels) := by
  rw [countablePiecewise_eq_sum_piecewise]
  exact IsSFinite.sum _ (fun index => (finite index).piecewise
    (IsSFinite.zero source target) _ (measurable index))

end

end Foundations.Measure.Kernel
