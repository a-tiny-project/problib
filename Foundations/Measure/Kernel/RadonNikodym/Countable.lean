module

public import Foundations.Measure.Kernel.RadonNikodym.SFinite
public import Foundations.Measure.Product.Countable

set_option autoImplicit false

/-!
# Kernel Radon-Nikodym derivatives: countable discrete sources

Constructs jointly measurable Radon-Nikodym derivatives for transition kernels
over a countable discrete source into an arbitrary measurable destination space,
given explicit s-finite witnesses and fiberwise zero-infinity absolute continuity.
-/

namespace Foundations.Measure.Kernel.RadonNikodymDerivative

universe u v

variable {α : Type u} {β : Type v} {target : Space β}
  {kernel reference : Kernel (Space.discrete α) target}

/-- Construct a jointly measurable Radon-Nikodym derivative certificate for kernels
over a countable discrete source into an arbitrary measurable destination space. -/
public noncomputable def ofCountableSource (code : α → Nat)
    (injective : Function.Injective code)
    (kernelFinite : ∀ input, Measure.SFinite (kernel input))
    (referenceFinite : ∀ input, Measure.SFinite (reference input))
    (continuous : ∀ input, Measure.ZeroInfinityAbsolutelyContinuous
      (kernel input) (reference input)) : RadonNikodymDerivative kernel reference := by
  let derivatives := fun input => Measure.RadonNikodymDerivative.ofSFiniteReference
    (kernelFinite input) (referenceFinite input) (continuous input)
  exact {
    density := fun input => (derivatives input).density
    densityMeasurable := ENNRealMeasurable.ofMeasurableMap
      (MeasurableMap.uncurry_ofCountableFirst code injective
        (fun input => (derivatives input).densityMeasurable.measurableMap))
    reconstruct := fun input => (derivatives input).reconstruct
  }

/-- Exact existence criterion under s-finite target and reference kernel families.
Over a countable discrete source, a kernel Radon-Nikodym derivative exists if
and only if target fibers are zero-infinity absolutely continuous with respect to
reference fibers. -/
public theorem nonempty_iff_ofCountableSource (code : α → Nat)
    (injective : Function.Injective code)
    (kernelFinite : ∀ input, Measure.SFinite (kernel input))
    (referenceFinite : ∀ input, Measure.SFinite (reference input)) :
    Nonempty (RadonNikodymDerivative kernel reference) ↔
      ∀ input, Measure.ZeroInfinityAbsolutelyContinuous (kernel input) (reference input) :=
  ⟨fun ⟨derivative⟩ => derivative.zeroInfinityAbsolutelyContinuous,
    fun continuous => ⟨ofCountableSource code injective kernelFinite referenceFinite continuous⟩⟩

end Foundations.Measure.Kernel.RadonNikodymDerivative
