module

public import Foundations.Measure.Kernel.RadonNikodym.Generated
public import Foundations.Measure.StandardBorel.Generator

set_option autoImplicit false

/-!
# Standard-Borel kernel Radon-Nikodym derivatives

Constructs a jointly measurable Radon-Nikodym derivative for transition kernels
into standard-Borel destinations. Both kernels provide global s-finiteness witnesses
under fiberwise zero-infinity absolute continuity.
-/

namespace Foundations.Measure.Kernel.RadonNikodymDerivative

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}
  {kernel reference : Kernel source target}

/-- Constructs a jointly measurable Radon-Nikodym derivative for kernels targeting
a standard-Borel space. Both kernels must provide global s-finiteness witnesses
under fiberwise zero-infinity absolute continuity. -/
public noncomputable def ofStandardBorel (presentation : StandardBorel target)
    (kernelFinite : IsSFinite kernel) (referenceFinite : IsSFinite reference)
    (continuous : ∀ input, Measure.ZeroInfinityAbsolutelyContinuous (kernel input) (reference input)) :
    RadonNikodymDerivative kernel reference :=
  ofCountableGenerator presentation.countableGenerator kernelFinite referenceFinite continuous

/-- A jointly measurable Radon-Nikodym derivative into a standard-Borel space exists
if and only if fiberwise zero-infinity absolute continuity holds, assuming both
kernels are s-finite. -/
public theorem nonempty_iff_ofStandardBorel (presentation : StandardBorel target)
    (kernelFinite : IsSFinite kernel) (referenceFinite : IsSFinite reference) :
    Nonempty (RadonNikodymDerivative kernel reference) ↔
      ∀ input, Measure.ZeroInfinityAbsolutelyContinuous (kernel input) (reference input) :=
  nonempty_iff_ofCountableGenerator presentation.countableGenerator kernelFinite referenceFinite

end Foundations.Measure.Kernel.RadonNikodymDerivative
