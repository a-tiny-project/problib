module

public import Foundations.Measure.Kernel.RadonNikodym.Components
public import Foundations.Measure.Kernel.RadonNikodym.Factor
public import Foundations.Measure.Kernel.RadonNikodym.SFinite
public import Foundations.Measure.Kernel.Reference

set_option autoImplicit false

/-!
# Countably generated kernel Radon-Nikodym derivatives

Constructs a jointly measurable Radon-Nikodym derivative for kernels targeting a
countably generated measurable space from global s-finiteness of both kernels and
fiberwise zero-infinity absolute continuity.
-/

namespace Foundations.Measure.Kernel.RadonNikodymDerivative

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}
  {kernel reference : Kernel source target}

/-- Constructs a jointly measurable Radon-Nikodym derivative for kernels into countably
generated spaces. The construction reduces through a globally finite reference
kernel preserving fiber null sets. -/
public noncomputable def ofCountableGenerator (generator : Space.CountableGenerator target)
    (kernelFinite : IsSFinite kernel) (referenceFinite : IsSFinite reference)
    (continuous : ∀ input, Measure.ZeroInfinityAbsolutelyContinuous (kernel input) (reference input)) :
    RadonNikodymDerivative kernel reference := by
  let base := FiniteReference.ofSFinite referenceFinite
  let referenceDerivative := ofSFiniteFiniteReference generator referenceFinite base.finite.measure
    base.targetContinuous
  let kernelDerivative := ofSFiniteFiniteReference generator kernelFinite base.finite.measure
    (fun input => Measure.AbsolutelyContinuous.trans (continuous input).absolutelyContinuous
      (base.targetContinuous input))
  exact ofCommonFiniteReference kernelDerivative referenceDerivative base.finite.measure
    (fun input => ⟨Measure.RadonNikodymDerivative.ofSFiniteReference (kernelFinite.measure input)
      (referenceFinite.measure input) (continuous input)⟩)

/-- A jointly measurable Radon-Nikodym derivative into a countably generated space
exists if and only if fiberwise zero-infinity absolute continuity holds, assuming
both kernels are s-finite. -/
public theorem nonempty_iff_ofCountableGenerator (generator : Space.CountableGenerator target)
    (kernelFinite : IsSFinite kernel) (referenceFinite : IsSFinite reference) :
    Nonempty (RadonNikodymDerivative kernel reference) ↔
      ∀ input, Measure.ZeroInfinityAbsolutelyContinuous (kernel input) (reference input) :=
  ⟨fun ⟨derivative⟩ => derivative.zeroInfinityAbsolutelyContinuous,
    fun continuous => ⟨ofCountableGenerator generator kernelFinite referenceFinite continuous⟩⟩

end Foundations.Measure.Kernel.RadonNikodymDerivative
