import Foundations.Measure.Giry.Basic
import Foundations.Measure.Kernel.Basic

set_option autoImplicit false

namespace Foundations.Measure.Giry

open Foundations.Real

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {source : Space α} {target : Space β} {result : Space γ}

/-- Convert an everywhere-probability kernel into a parameter-indexed family of
probability laws. -/
def ofKernel (kernel : Kernel source target)
    (normalized : ∀ input, Measure.IsProbability (kernel input)) :
    α → Law target := fun input => ⟨kernel input, normalized input⟩

/-- The law family induced by an everywhere-probability kernel is a
measurable map into `space target`. -/
theorem ofKernel_measurable (kernel : Kernel source target)
    (normalized : ∀ input, Measure.IsProbability (kernel input)) :
    MeasurableMap source (space target) (ofKernel kernel normalized) :=
  (measurable_iff _).mpr kernel.measurable

/-- Convert a measurable family of probability laws into a probability
kernel. -/
noncomputable def toKernel (family : α → Law target)
    (measurable : MeasurableMap source (space target) family) :
    Kernel source target where
  toFun := fun input => (family input).val
  measurable := (measurable_iff family).mp measurable

/-- Every fiber of the kernel converted from a law family is a probability
measure. -/
theorem toKernel_probability (family : α → Law target)
    (measurable : MeasurableMap source (space target) family) (input : α) :
    Measure.IsProbability (toKernel family measurable input) :=
  (family input).property

/-- A kernel converted from a probability law family is finite with total mass
bounded by 1. -/
theorem toKernel_finite (family : α → Law target)
    (measurable : MeasurableMap source (space target) family) :
    Kernel.IsFinite (toKernel family measurable) := by
  refine ⟨⟨ENNReal.one, True.intro, ?_⟩⟩
  intro input
  rw [(toKernel_probability family measurable input).univ_eq_one]
  exact ENNReal.leRefl _

/-- The universal evaluation kernel on `space target`, corresponding to the
identity map on laws. -/
noncomputable def evaluationKernel (target : Space β) :
    Kernel (space target) target :=
  toKernel (fun law => law) (MeasurableMap.identity (space target))

/-- Round-trip identity: converting an everywhere-probability kernel to a law
family and back recovers the original kernel. -/
theorem toKernel_ofKernel (kernel : Kernel source target)
    (normalized : ∀ input, Measure.IsProbability (kernel input)) :
    toKernel (ofKernel kernel normalized)
      (ofKernel_measurable kernel normalized) = kernel := by
  apply Kernel.ext
  intro input
  rfl

/-- Round-trip identity: converting a measurable law family to a kernel and
back recovers the original family. -/
theorem ofKernel_toKernel (family : α → Law target)
    (measurable : MeasurableMap source (space target) family) :
    ofKernel (toKernel family measurable)
      (toKernel_probability family measurable) = family := by
  funext input
  rfl

/-- Universal kernel characterization: a kernel represents a measurable law
family if and only if every fiber is a probability measure. -/
theorem representation_iff (kernel : Kernel source target) :
    (∃ family, ∃ measurable : MeasurableMap source (space target) family,
      toKernel family measurable = kernel) ↔
      ∀ input, Measure.IsProbability (kernel input) := by
  constructor
  · rintro ⟨family, measurable, rfl⟩
    exact toKernel_probability family measurable
  · intro normalized
    exact ⟨ofKernel kernel normalized, ofKernel_measurable kernel normalized,
      toKernel_ofKernel kernel normalized⟩

end Foundations.Measure.Giry
