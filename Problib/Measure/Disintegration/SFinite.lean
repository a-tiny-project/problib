module

public import Problib.Measure.Disintegration.Compatibility
public import Problib.Measure.Disintegration.StandardBorel
public import Problib.Measure.Decomposition.ZeroInfinity.Construction

set_option autoImplicit false

namespace Problib.Measure.Measure.Disintegration

open Problib.Real

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {parameter : Space beta}

/-- Construct a disintegration for an s-finite zero-infinity joint measure over a standard-Borel conditioned space and arbitrary parameter space. -/
@[expose] public noncomputable def ofZeroInfinity
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SFinite joint) (pure : IsZeroInfinitySet joint Set.univ) : Disintegration joint := by
  let reference := FiniteReference.ofSFinite finite
  let marginalFinite : SigmaFinite (secondMarginal reference.reference) :=
    SigmaFinite.ofFinite (reference.finite.map Prod.snd (Space.second_measurable source parameter))
  let selection := ofStandardBorel reference.reference presentation marginalFinite
  refine {
    conditional := selection.conditional
    conditionalSFinite := selection.conditionalSFinite
    reconstruction := ?_
  }
  have scaled := (selection.smul ENNReal.top).reconstruction
  change reverseSemiproduct (secondMarginal (Measure.smul ENNReal.top reference.reference))
    selection.conditional selection.conditionalSFinite = Measure.smul ENNReal.top reference.reference at scaled
  rw [← pure.eq_smul_top reference] at scaled
  exact scaled

/-- Every fiber of the zero-infinity disintegration has total mass at most one. -/
public theorem ofZeroInfinity_univ_le_one
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SFinite joint) (pure : IsZeroInfinitySet joint Set.univ) (input : beta) :
    ENNReal.le ((ofZeroInfinity joint presentation finite pure).conditional input Set.univ) ENNReal.one :=
  ofStandardBorel_univ_le_one _ _ _ input

/-- The conditional kernel of the zero-infinity disintegration is uniformly finite with bound one. -/
public theorem ofZeroInfinity_isFinite
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SFinite joint) (pure : IsZeroInfinitySet joint Set.univ) :
    Kernel.IsFinite (ofZeroInfinity joint presentation finite pure).conditional :=
  ⟨⟨ENNReal.one, True.intro, ofZeroInfinity_univ_le_one joint presentation finite pure⟩⟩

/-- The conditional kernel of the zero-infinity disintegration has probability fibers almost everywhere under its second marginal. -/
public theorem ofZeroInfinity_isProbability_ae
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SFinite joint) (pure : IsZeroInfinitySet joint Set.univ) :
    (secondMarginal joint).AE
      (fun input => IsProbability ((ofZeroInfinity joint presentation finite pure).conditional input)) := by
  let reference := FiniteReference.ofSFinite finite
  let marginalFinite : SigmaFinite (secondMarginal reference.reference) :=
    SigmaFinite.ofFinite (reference.finite.map Prod.snd (Space.second_measurable source parameter))
  have normalized := (ofStandardBorel reference.reference presentation marginalFinite).isProbability_ae marginalFinite
  exact AbsolutelyContinuous.ae (AbsolutelyContinuous.map reference.target_continuous Prod.snd
    (Space.second_measurable source parameter)) normalized

/-- Construct a disintegration for an s-finite joint measure with compatible infinite parts over a standard-Borel conditioned space and arbitrary parameter space. -/
@[expose] public noncomputable def ofSFinite (joint : Measure (Space.product source parameter))
    (presentation : StandardBorel source) (finite : SFinite joint)
    (jointTop : TopZeroInfinitySet joint) (marginalTop : TopZeroInfinitySet (secondMarginal joint))
    (compatible : InfinitePartCompatible joint jointTop marginalTop) : Disintegration joint := by
  have measurable := marginalTop.zero_infinity.measurable
  have insideMeasurable := Space.second_measurable source parameter measurable
  let inside := ofZeroInfinity (joint.restrict (Set.preimage Prod.snd marginalTop.set)) presentation
    (finite.restrict insideMeasurable)
    ((isZeroInfinitySet_restrict_univ_iff joint insideMeasurable).mpr
      ((infinitePartCompatible_iff joint jointTop marginalTop).mp compatible))
  have outsideFinite : SigmaFinite (secondMarginal
      (joint.restrict (Set.preimage Prod.snd (Set.complement marginalTop.set)))) := by
    rw [secondMarginal_restrict_second joint (parameter.complement measurable)]
    exact marginalTop.sigmaFinite_complement (secondMarginalSFinite finite)
  let outside := ofStandardBorel
    (joint.restrict (Set.preimage Prod.snd (Set.complement marginalTop.set))) presentation outsideFinite
  exact piecewise joint measurable inside outside

/-- Every fiber of the s-finite disintegration has total mass at most one. -/
public theorem ofSFinite_univ_le_one (joint : Measure (Space.product source parameter))
    (presentation : StandardBorel source) (finite : SFinite joint)
    (jointTop : TopZeroInfinitySet joint) (marginalTop : TopZeroInfinitySet (secondMarginal joint))
    (compatible : InfinitePartCompatible joint jointTop marginalTop) (input : beta) :
    ENNReal.le ((ofSFinite joint presentation finite jointTop marginalTop compatible).conditional input Set.univ)
      ENNReal.one := by
  change ENNReal.le (Kernel.piecewise marginalTop.set marginalTop.zero_infinity.measurable
    _ _ input Set.univ) ENNReal.one
  classical
  by_cases member : marginalTop.set input
  · rw [Kernel.piecewise_apply_of_mem _ _ _ _ _ member]
    exact ofZeroInfinity_univ_le_one _ _ _ _ input
  · rw [Kernel.piecewise_apply_of_not_mem _ _ _ _ _ member]
    exact ofStandardBorel_univ_le_one _ _ _ input

/-- The conditional kernel of the s-finite disintegration is uniformly finite with bound one. -/
public theorem ofSFinite_isFinite (joint : Measure (Space.product source parameter))
    (presentation : StandardBorel source) (finite : SFinite joint)
    (jointTop : TopZeroInfinitySet joint) (marginalTop : TopZeroInfinitySet (secondMarginal joint))
    (compatible : InfinitePartCompatible joint jointTop marginalTop) :
    Kernel.IsFinite (ofSFinite joint presentation finite jointTop marginalTop compatible).conditional :=
  ⟨⟨ENNReal.one, True.intro,
    ofSFinite_univ_le_one joint presentation finite jointTop marginalTop compatible⟩⟩

/-- The conditional kernel of the s-finite disintegration has probability fibers almost everywhere under its second marginal. -/
public theorem ofSFinite_isProbability_ae (joint : Measure (Space.product source parameter))
    (presentation : StandardBorel source) (finite : SFinite joint)
    (jointTop : TopZeroInfinitySet joint) (marginalTop : TopZeroInfinitySet (secondMarginal joint))
    (compatible : InfinitePartCompatible joint jointTop marginalTop) :
    (secondMarginal joint).AE (fun input => IsProbability
      ((ofSFinite joint presentation finite jointTop marginalTop compatible).conditional input)) := by
  unfold ofSFinite
  apply piecewise_isProbability_ae
  · exact ofZeroInfinity_isProbability_ae _ _ _ _
  · apply isProbability_ae
    rw [secondMarginal_restrict_second joint (parameter.complement marginalTop.zero_infinity.measurable)]
    exact marginalTop.sigmaFinite_complement (secondMarginalSFinite finite)

/-- Construct an everywhere-probability disintegration for an s-finite joint measure with compatible infinite parts given an explicit fallback point. -/
@[expose] public noncomputable def ofSFiniteProbability
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SFinite joint) (jointTop : TopZeroInfinitySet joint)
    (marginalTop : TopZeroInfinitySet (secondMarginal joint))
    (compatible : InfinitePartCompatible joint jointTop marginalTop) (fallback : alpha) : Disintegration joint :=
  (ofSFinite joint presentation finite jointTop marginalTop compatible).probabilityVersion
    (ofSFinite_isProbability_ae joint presentation finite jointTop marginalTop compatible) fallback

/-- Every fiber of the everywhere-probability s-finite disintegration is a probability measure. -/
public theorem ofSFiniteProbability_isProbability
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SFinite joint) (jointTop : TopZeroInfinitySet joint)
    (marginalTop : TopZeroInfinitySet (secondMarginal joint))
    (compatible : InfinitePartCompatible joint jointTop marginalTop) (fallback : alpha) (input : beta) :
    IsProbability ((ofSFiniteProbability joint presentation finite jointTop marginalTop compatible fallback).conditional input) :=
  probabilityVersion_isProbability _ _ _ _

/-- An s-finite joint measure over a standard-Borel conditioned space has a disintegration if and only if its infinite parts are compatible. -/
public theorem nonempty_iff_infinitePartCompatible
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SFinite joint) (jointTop : TopZeroInfinitySet joint)
    (marginalTop : TopZeroInfinitySet (secondMarginal joint)) :
    Nonempty (Disintegration joint) ↔ InfinitePartCompatible joint jointTop marginalTop :=
  ⟨fun ⟨selection⟩ => selection.infinitePartCompatible finite jointTop marginalTop,
    fun compatible => ⟨ofSFinite joint presentation finite jointTop marginalTop compatible⟩⟩

end Problib.Measure.Measure.Disintegration
