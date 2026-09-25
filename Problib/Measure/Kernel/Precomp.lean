module

public import Problib.Measure.Kernel.Basic

set_option autoImplicit false

/-!
# Source precomposition of transition kernels

Precomposes transition kernels with measurable functions on the source space.
Establishes identity, functorial composition, sum commuting, pushforward
commuting, and finiteness preservation.
-/
namespace Problib.Measure.Kernel

public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {parameter : Space α} {source : Space β} {target : Space γ} {result : Space δ}

/-- Precompose a transition kernel with a measurable function on its source
space. -/
@[expose] noncomputable def precomp (kernel : Kernel source target)
    (function : α → β) (measurable : MeasurableMap parameter source function) :
    Kernel parameter target where
  toFun := fun input => kernel (function input)
  measurable := fun setMeasurable =>
    ENNRealMeasurable.comp (kernel.measurable setMeasurable) measurable

/-- Evaluate a precomposed transition kernel at an input point. -/
@[simp] theorem precomp_apply (kernel : Kernel source target)
    (function : α → β) (measurable : MeasurableMap parameter source function) (input : α) :
    kernel.precomp function measurable input = kernel (function input) := rfl

/-- Precomposition with the identity measurable map recovers the original
kernel. -/
@[simp] theorem precomp_id (kernel : Kernel source target) :
    kernel.precomp (fun input => input) (MeasurableMap.identity source) = kernel := by
  apply Kernel.ext
  intro input
  rfl

/-- Successive precompositions correspond to precomposition with the composite
measurable map. -/
theorem precomp_comp (kernel : Kernel target result)
    (before : α → β) (beforeMeasurable : MeasurableMap parameter source before)
    (after : β → γ) (afterMeasurable : MeasurableMap source target after) :
    (kernel.precomp after afterMeasurable).precomp before beforeMeasurable =
      kernel.precomp (fun input => after (before input))
        (MeasurableMap.comp afterMeasurable beforeMeasurable) := by
  apply Kernel.ext
  intro input
  rfl

/-- Precomposition distributes over countable sums of transition kernels. -/
theorem precomp_sum (kernels : Nat → Kernel source target)
    (function : α → β) (measurable : MeasurableMap parameter source function) :
    (Kernel.sum kernels).precomp function measurable =
      Kernel.sum (fun index => (kernels index).precomp function measurable) := by
  apply Kernel.ext
  intro input
  rfl

/-- Source precomposition commutes with target pushforward of transition
kernels. -/
theorem precomp_map (kernel : Kernel source target)
    (before : α → β) (beforeMeasurable : MeasurableMap parameter source before)
    (after : γ → δ) (afterMeasurable : MeasurableMap target result after) :
    (kernel.map after afterMeasurable).precomp before beforeMeasurable =
      (kernel.precomp before beforeMeasurable).map after afterMeasurable := by
  apply Kernel.ext
  intro input
  rfl

/-- Source precomposition preserves uniform finiteness of transition
kernels. -/
theorem IsFinite.precomp {kernel : Kernel source target} (finite : IsFinite kernel)
    (function : α → β) (measurable : MeasurableMap parameter source function) :
    IsFinite (kernel.precomp function measurable) := by
  rcases finite.exists_bound with ⟨bound, boundFinite, bounded⟩
  exact ⟨⟨bound, boundFinite, fun input => bounded (function input)⟩⟩

/-- Source precomposition preserves s-finiteness of transition kernels. -/
noncomputable def IsSFinite.precomp {kernel : Kernel source target}
    (finite : IsSFinite kernel) (function : α → β)
    (measurable : MeasurableMap parameter source function) :
    IsSFinite (kernel.precomp function measurable) where
  components := fun index => (finite.components index).precomp function measurable
  finite := fun index => (finite.finite index).precomp function measurable
  sum_eq := by
    rw [← precomp_sum, finite.sum_eq]

end

end Problib.Measure.Kernel
