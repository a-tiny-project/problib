module

public import Foundations.Measure.Kernel.RadonNikodym.Basic
public import Foundations.Measure.Decomposition.RadonNikodym.SFiniteReference
public import Foundations.Measure.Decomposition.RadonNikodym.Uniqueness

set_option autoImplicit false

/-!
# Kernel Radon-Nikodym derivatives: s-finite properties

Establishes necessity of fiberwise zero-infinity absolute continuity and
almost-everywhere-infinity uniqueness for s-finite reference kernels. Ordinary
equality holds almost everywhere off the greatest zero-infinity set. On that
set, densities agree on zero versus nonzero values almost everywhere.
-/

namespace Foundations.Measure.Kernel.RadonNikodymDerivative

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}
  {kernel reference : Kernel source target}

/-- Fiberwise zero-infinity absolute continuity of target with respect to reference. -/
public theorem zeroInfinityAbsolutelyContinuous
    (derivative : RadonNikodymDerivative kernel reference) (input : α) :
    Measure.ZeroInfinityAbsolutelyContinuous (kernel input) (reference input) :=
  (derivative.fiber input).zeroInfinityAbsolutelyContinuous

/-- Uniqueness of kernel densities modulo zero-infinity regions under s-finite
reference fibers and supplied greatest zero-infinity sets. Ordinary equality
holds almost everywhere off the greatest zero-infinity set. On that set, the
theorem identifies zero versus nonzero values almost everywhere, rather than
their positive magnitudes. -/
public theorem density_aeInfinityEq (left right : RadonNikodymDerivative kernel reference)
    (finite : ∀ input, Measure.SFinite (reference input))
    (top : ∀ input, Measure.TopZeroInfinitySet (reference input)) (input : α) :
    (top input).AEInfinityEq (left.density input) (right.density input) :=
  (left.fiber input).density_aeInfinityEq (right.fiber input) (finite input) (top input)

end Foundations.Measure.Kernel.RadonNikodymDerivative
