module

public import Problib.Measure.Kernel.RadonNikodym.Generated
public import Problib.Measure.StandardBorel.Generator
public import Problib.Measure.Decomposition.ZeroInfinity.AbsoluteContinuity

set_option autoImplicit false

/-!
# Standard-Borel kernel Radon-Nikodym derivatives

Constructs a jointly measurable Radon-Nikodym derivative for transition kernels
into standard-Borel destinations. Both kernels provide global s-finiteness witnesses
under fiberwise zero-infinity absolute continuity.
-/

namespace Problib.Measure.Kernel.RadonNikodymDerivative

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

/-- Constructs the derivative from plain absolute continuity when every reference
fiber is sigma-finite: a sigma-finite reference has no zero-infinity sets but
null ones, so absolute continuity already preserves them. -/
public noncomputable def ofStandardBorelSigmaFinite (presentation : StandardBorel target)
    (kernelFinite : IsSFinite kernel) (referenceFinite : IsSFinite reference)
    (fibers : ∀ input, Measure.SigmaFinite (reference input))
    (continuous : ∀ input, Measure.AbsolutelyContinuous (kernel input) (reference input)) :
    RadonNikodymDerivative kernel reference :=
  ofStandardBorel presentation kernelFinite referenceFinite fun input =>
    (Measure.ZeroInfinityAbsolutelyContinuous.iff_absolutelyContinuous_of_sigmaFinite
      (fibers input)).mpr (continuous input)

/-- A jointly measurable Radon-Nikodym derivative into a standard-Borel space exists
if and only if fiberwise zero-infinity absolute continuity holds, assuming both
kernels are s-finite. -/
public theorem nonempty_iff_of_standardBorel (presentation : StandardBorel target)
    (kernelFinite : IsSFinite kernel) (referenceFinite : IsSFinite reference) :
    Nonempty (RadonNikodymDerivative kernel reference) ↔
      ∀ input, Measure.ZeroInfinityAbsolutelyContinuous (kernel input) (reference input) :=
  nonempty_iff_of_countableGenerator presentation.countableGenerator kernelFinite referenceFinite

end Problib.Measure.Kernel.RadonNikodymDerivative
