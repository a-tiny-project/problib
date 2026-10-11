module

public import Problib.Measure.Additive.Marginal
public import Problib.Measure.Decomposition.ZeroInfinity.Properties

set_option autoImplicit false

namespace Problib.Measure

open Problib.Real

universe u v

namespace Measure

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- The marginal infinite part not covered by the joint infinite part. -/
@[expose] public def infinitePartMismatchSet
    {joint : Measure (Space.product source target)}
    (jointTop : TopZeroInfinitySet joint)
    (marginalTop : TopZeroInfinitySet (secondMarginal joint)) :
    Set (alpha × beta) :=
  Set.difference
    (Set.preimage Prod.snd marginalTop.set)
    jointTop.set

public theorem infinitePartMismatchSet_measurable
    {joint : Measure (Space.product source target)}
    (jointTop : TopZeroInfinitySet joint)
    (marginalTop : TopZeroInfinitySet (secondMarginal joint)) :
    (Space.product source target).Measurable
      (infinitePartMismatchSet jointTop marginalTop) :=
  (Space.product source target).difference
    (Space.second_measurable source target
      marginalTop.zero_infinity.measurable)
    jointTop.zero_infinity.measurable

/-- The marginal and joint zero-infinity decompositions agree almost
everywhere on the marginal infinite part. -/
@[expose] public def InfinitePartCompatible
    (joint : Measure (Space.product source target))
    (jointTop : TopZeroInfinitySet joint)
    (marginalTop : TopZeroInfinitySet (secondMarginal joint)) : Prop :=
  joint (infinitePartMismatchSet jointTop marginalTop) =
    ENNReal.zero

/-- Infinite-part compatibility holds if and only if the joint measure is zero-infinity on the inverse image of the marginal infinite region. -/
public theorem infinitePartCompatible_iff
    (joint : Measure (Space.product source target))
    (jointTop : TopZeroInfinitySet joint)
    (marginalTop : TopZeroInfinitySet (secondMarginal joint)) :
    InfinitePartCompatible joint jointTop marginalTop ↔
      IsZeroInfinitySet joint (Set.preimage Prod.snd marginalTop.set) :=
  ⟨fun compatible => IsZeroInfinitySet.of_null_difference
    (Space.second_measurable source target marginalTop.zero_infinity.measurable)
    jointTop.zero_infinity compatible,
    fun pure => jointTop.greatest pure⟩

end Measure

end Problib.Measure
