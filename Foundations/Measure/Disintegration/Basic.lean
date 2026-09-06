module

public import Foundations.Measure.Additive.Marginal
public import Foundations.Measure.Decomposition.ZeroInfinity.Properties

set_option autoImplicit false

namespace Foundations.Measure

open Foundations.Real

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
      marginalTop.zeroInfinity.measurable)
    jointTop.zeroInfinity.measurable

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
    (Space.second_measurable source target marginalTop.zeroInfinity.measurable)
    jointTop.zeroInfinity compatible,
    fun pure => jointTop.greatest pure⟩

end Measure

end Foundations.Measure
