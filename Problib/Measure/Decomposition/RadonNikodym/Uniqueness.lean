module

public import Problib.Measure.Decomposition.RadonNikodym.Basic
public import Problib.Measure.Decomposition.ZeroInfinity.Uniqueness

/-!
# Radon-Nikodym derivative uniqueness

This module proves that Radon-Nikodym derivative certificates for the same
target measure are almost-everywhere-infinity equal under an s-finite
reference measure.
-/

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Radon-Nikodym derivatives for the same target measure are
almost-everywhere-infinity equal under an s-finite reference measure. -/
public theorem RadonNikodymDerivative.density_aeInfinityEq
    {target reference : Measure space}
    (left right : RadonNikodymDerivative target reference)
    (finite : SFinite reference) (top : TopZeroInfinitySet reference) :
    top.AEInfinityEq left.density right.density :=
  left.reconstruct.aeInfinityEq right.reconstruct finite top
    left.density_measurable right.density_measurable

end Problib.Measure.Measure
