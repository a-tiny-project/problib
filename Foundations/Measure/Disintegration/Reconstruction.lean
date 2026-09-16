module

public import Foundations.Measure.Additive.Marginal
public import Foundations.Measure.Kernel.Product.Basic

set_option autoImplicit false

namespace Foundations.Measure

universe u v

namespace Measure

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- A conditional kernel reconstructs the joint measure from its second
marginal. -/
@[expose] public def Disintegrates
    (joint : Measure (Space.product source target))
    (kernel : Kernel target source)
    (kernelSFinite : Kernel.IsSFinite kernel) : Prop :=
  Measure.reverseSemiproduct
    (Measure.secondMarginal joint) kernel kernelSFinite =
      joint

/-- A selected conditional kernel with its exact reconstruction certificate. -/
public structure Disintegration
    (joint : Measure (Space.product source target)) :
    Type (max u v) where
  conditional : Kernel target source
  conditionalSFinite : Kernel.IsSFinite conditional
  reconstruction :
    Disintegrates joint conditional conditionalSFinite

/-- Extract the exact reverse-semiproduct reconstruction certificate from a
disintegration package. -/
public theorem Disintegration.disintegrates
    {joint : Measure (Space.product source target)}
    (disintegration : Disintegration joint) :
    Disintegrates joint disintegration.conditional
      disintegration.conditionalSFinite :=
  disintegration.reconstruction

end Measure

end Foundations.Measure
