module

public import Foundations.Measure.Disintegration.Basic
public import Foundations.Measure.Disintegration.Algebra
public import Foundations.Measure.Decomposition.ZeroInfinity.Product

set_option autoImplicit false

namespace Foundations.Measure.Measure.Disintegration

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {parameter : Space beta}
  {joint : Measure (Space.product source parameter)}

/-- Any existing disintegration of an s-finite joint measure has compatible infinite parts. -/
public theorem infinitePartCompatible (selection : Disintegration joint) (finite : SFinite joint)
    (jointTop : TopZeroInfinitySet joint) (marginalTop : TopZeroInfinitySet (secondMarginal joint)) :
    InfinitePartCompatible joint jointTop marginalTop := by
  have measurable := marginalTop.zeroInfinity.measurable
  have pure := (isZeroInfinitySet_restrict_univ_iff (secondMarginal joint) measurable).mpr
    marginalTop.zeroInfinity
  have productPure := pure.reverseSemiproduct
    ((secondMarginalSFinite finite).restrict measurable) selection.conditional selection.conditionalSFinite
  rw [← secondMarginal_restrict_second joint measurable] at productPure
  change IsZeroInfinitySet (reverseSemiproduct
    (secondMarginal (joint.restrict (Set.preimage Prod.snd marginalTop.set)))
    (selection.restrict measurable).conditional (selection.restrict measurable).conditionalSFinite)
    Set.univ at productPure
  rw [(selection.restrict measurable).reconstruction] at productPure
  exact (infinitePartCompatible_iff joint jointTop marginalTop).mpr
    ((isZeroInfinitySet_restrict_univ_iff joint
      (Space.second_measurable source parameter measurable)).mp productPure)

end Foundations.Measure.Measure.Disintegration
