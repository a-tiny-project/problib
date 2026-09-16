module

public import Foundations.Measure.Additive.SFinite
public import Foundations.Measure.Integral.Density.Uniqueness

set_option autoImplicit false

namespace Foundations.Measure

open Foundations.Real

universe u

namespace Measure

variable {alpha : Type u} {space : Space alpha}

/-- A measurable density reconstructing one measure from another. -/
public structure RadonNikodymDerivative
    (target reference : Measure space) : Type u where
  density : alpha → ENNReal
  densityMeasurable : ENNRealMeasurable space density
  reconstruct : IsDensity target reference density

/-- The selected derivative reconstructs the target measure. -/
public theorem RadonNikodymDerivative.reconstruct_eq
    {target reference : Measure space}
    (derivative : RadonNikodymDerivative target reference) :
    target = reference.withDensity derivative.density :=
  derivative.reconstruct.eq_withDensity

/-- Any Radon-Nikodym derivative certificate yields absolute continuity through
its underlying density reconstruction certificate. -/
public theorem RadonNikodymDerivative.absolutelyContinuous
    {target reference : Measure space}
    (derivative : RadonNikodymDerivative target reference) :
    AbsolutelyContinuous target reference :=
  derivative.reconstruct.absolutelyContinuous

/-- Densities in two Radon-Nikodym derivative certificates for the same target
measure agree almost everywhere under a sigma-finite reference measure. -/
public theorem RadonNikodymDerivative.density_ae_eq
    {target reference : Measure space}
    (left right : RadonNikodymDerivative target reference)
    (finite : SigmaFinite reference) :
    reference.AEEq left.density right.density :=
  left.reconstruct.ae_eq right.reconstruct finite
    left.densityMeasurable right.densityMeasurable

end Measure

end Foundations.Measure
