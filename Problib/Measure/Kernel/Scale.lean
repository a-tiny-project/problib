module

public import Problib.Measure.Kernel.Basic

set_option autoImplicit false

/-!
# Scalar scaling of transition kernels

Defines scalar multiplication of transition kernels by extended nonnegative real
factors and proves preservation of global kernel finiteness.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Scalar multiplication of a transition kernel by an extended nonnegative real factor. -/
@[expose] public noncomputable def smul (factor : ENNReal) (kernel : Kernel source target) :
    Kernel source target where
  toFun := fun input => Measure.smul factor (kernel input)
  measurable := by
    intro set measurable
    have equal : (fun input => Measure.smul factor (kernel input) set) =
        (fun input => ENNReal.mul factor (kernel input set)) := by
      funext input
      exact Measure.smul_apply_measurable factor (kernel input) measurable
    rw [equal]
    exact (kernel.measurable measurable).const_mul factor

/-- Fiberwise evaluation of a scaled transition kernel. -/
@[simp] public theorem smul_apply (factor : ENNReal) (kernel : Kernel source target) (input : α) :
    smul factor kernel input = Measure.smul factor (kernel input) := rfl

/-- Scaling a globally finite transition kernel by a finite factor preserves global finiteness. -/
public theorem IsFinite.smul {kernel : Kernel source target} (finite : IsFinite kernel)
    (factor : ENNReal) (factorFinite : ENNReal.Finite factor) : IsFinite (Kernel.smul factor kernel) := by
  rcases finite.exists_bound with ⟨bound, boundFinite, bounded⟩
  refine ⟨⟨ENNReal.mul factor bound, ENNReal.mul_finite factorFinite boundFinite, ?_⟩⟩
  intro input
  rw [smul_apply, Measure.smul_apply_measurable _ _ target.univ]
  exact ENNReal.mul_le_mul (ENNReal.le_refl factor) (bounded input)

end Problib.Measure.Kernel
