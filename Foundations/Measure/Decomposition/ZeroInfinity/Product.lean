module

public import Foundations.Measure.Decomposition.ZeroInfinity.Properties
public import Foundations.Measure.Decomposition.ZeroInfinity.Reference
public import Foundations.Measure.Kernel.Product.Algebra

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}

/-- The reverse semiproduct of an s-finite zero-infinity base measure and an s-finite kernel is a zero-infinity measure on the product space. -/
public theorem IsZeroInfinitySet.reverseSemiproduct {measure : Measure target}
    (pure : IsZeroInfinitySet measure Set.univ) (finite : SFinite measure)
    (kernel : Kernel target source) (kernelFinite : Kernel.IsSFinite kernel) :
    IsZeroInfinitySet (Measure.reverseSemiproduct measure kernel kernelFinite) Set.univ := by
  let reference := FiniteReference.ofSFinite finite
  rw [pure.eq_smul_top reference, Measure.reverseSemiproduct_smul]
  exact IsZeroInfinitySet.smul_top _

end Foundations.Measure.Measure
