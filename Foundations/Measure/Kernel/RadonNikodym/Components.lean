module

public import Foundations.Measure.Kernel.RadonNikodym.Finite

set_option autoImplicit false

/-!
# S-finite kernel Radon-Nikodym components

Decomposes an s-finite kernel into countably many finite components against a
reference kernel with finite fibers. Sums component derivatives under ordinary
absolute continuity into a joint density.
-/

namespace Foundations.Measure.Kernel.RadonNikodymDerivative

open Foundations.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}
  {kernel reference : Kernel source target}

/-- Sum of countable kernel Radon-Nikodym derivatives with respect to a fixed
reference kernel, obtaining a derivative for the sum kernel. -/
public noncomputable def sum (kernels : Nat → Kernel source target)
    (derivatives : ∀ index, RadonNikodymDerivative (kernels index) reference) :
    RadonNikodymDerivative (Kernel.sum kernels) reference where
  density := fun input output => ENNReal.tsum (fun index => (derivatives index).density input output)
  densityMeasurable := ENNRealMeasurable.tsum (fun index => (derivatives index).densityMeasurable)
  reconstruct := by
    intro input
    change Measure.sum (fun index => kernels index input) = (reference input).withDensity _
    rw [(reference input).withDensity_tsum (fun index => (derivatives index).density input)
      (fun index => jointlyMeasurable_slice (derivatives index).densityMeasurable input)]
    exact congrArg Measure.sum (funext (fun index => (derivatives index).reconstruct input))

/-- Constructs a jointly measurable kernel Radon-Nikodym derivative for an s-finite
kernel targeting a countably generated space against a reference kernel with finite individual fibers.
The construction sums derivatives of the finite components under ordinary absolute continuity. -/
public noncomputable def ofSFiniteFiniteReference (generator : Space.CountableGenerator target)
    (kernelFinite : IsSFinite kernel) (referenceFinite : ∀ input, Measure.IsFinite (reference input))
    (continuous : ∀ input, Measure.AbsolutelyContinuous (kernel input) (reference input)) :
    RadonNikodymDerivative kernel reference := by
  have componentContinuous : ∀ index input,
      Measure.AbsolutelyContinuous (kernelFinite.components index input) (reference input) := by
    intro index input
    apply Measure.AbsolutelyContinuous.of_le (continuous input)
    intro set _
    have bound := Measure.le_sum (fun index => kernelFinite.components index input) index set
    change ENNReal.le _ (Kernel.sum kernelFinite.components input set) at bound
    rw [kernelFinite.sum_eq] at bound
    exact bound
  let derivatives := fun index => ofFiniteFibers generator (kernelFinite.finite index).measure
    referenceFinite (componentContinuous index)
  have combined := sum kernelFinite.components derivatives
  rw [kernelFinite.sum_eq] at combined
  exact combined

end Foundations.Measure.Kernel.RadonNikodymDerivative
