module

public import Problib.Measure.Kernel.RadonNikodym.Basic
public import Problib.Measure.Extended.Ratio

set_option autoImplicit false

/-!
# Common finite reference kernel Radon-Nikodym derivatives

Forms the ratio density of two kernels over a common base kernel with finite
fibers through `ENNReal.densityRatio`. Fiberwise factorability proves exact reconstruction.
-/

namespace Problib.Measure.Kernel.RadonNikodymDerivative

open Problib.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}
  {kernel reference base : Kernel source target}

/-- Constructs a jointly measurable Radon-Nikodym derivative between two kernels
sharing a common reference kernel with finite individual fibers. The density is
the pointwise ratio, and fiber reconstruction follows from fiberwise factorability. -/
public noncomputable def ofCommonFiniteReference
    (kernelDerivative : RadonNikodymDerivative kernel base)
    (referenceDerivative : RadonNikodymDerivative reference base)
    (finite : ∀ input, Measure.IsFinite (base input))
    (factorable : ∀ input, Nonempty (Measure.RadonNikodymDerivative (kernel input) (reference input))) :
    RadonNikodymDerivative kernel reference where
  density := fun input output => ENNReal.densityRatio (kernelDerivative.density input output)
    (referenceDerivative.density input output)
  density_measurable := kernelDerivative.density_measurable.densityRatio referenceDerivative.density_measurable
  reconstruct := by
    intro input
    rcases factorable input with ⟨derivative⟩
    let left := kernelDerivative.density input
    let right := referenceDerivative.density input
    let ratio := fun value => ENNReal.densityRatio (left value) (right value)
    have leftMeasurable : ENNRealMeasurable target left :=
      jointly_measurable_slice kernelDerivative.density_measurable input
    have rightMeasurable : ENNRealMeasurable target right :=
      jointly_measurable_slice referenceDerivative.density_measurable input
    have ratioMeasurable : ENNRealMeasurable target ratio := leftMeasurable.densityRatio rightMeasurable
    have factorization : (base input).withDensity left =
        (base input).withDensity (fun value => ENNReal.mul (right value) (derivative.density value)) := by
      rw [← (base input).withDensity_withDensity rightMeasurable derivative.density_measurable,
        ← referenceDerivative.reconstruct input, ← kernelDerivative.reconstruct input]
      exact derivative.reconstruct_eq
    have equal := Measure.aeEq_of_withDensity_eq (Measure.SigmaFinite.ofFinite (finite input))
      leftMeasurable (rightMeasurable.mul derivative.density_measurable) factorization
    have restored : (base input).AEEq (fun value => ENNReal.mul (right value) (ratio value)) left := by
      apply equal.mono
      intro value equation
      change ENNReal.mul (right value) (ENNReal.densityRatio (left value) (right value)) = left value
      rw [equation]
      exact ENNReal.mul_densityRatio (right value) (derivative.density value)
    change kernel input = (reference input).withDensity ratio
    rw [referenceDerivative.reconstruct input,
      (base input).withDensity_withDensity rightMeasurable ratioMeasurable,
      Measure.withDensity_congr_ae restored]
    exact kernelDerivative.reconstruct input

end Problib.Measure.Kernel.RadonNikodymDerivative
