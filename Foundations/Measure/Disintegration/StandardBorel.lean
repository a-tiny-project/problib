module

public import Foundations.Measure.Disintegration.Embedding
public import Foundations.Measure.Disintegration.Probability
public import Foundations.Measure.Disintegration.Unit
public import Foundations.Measure.StandardBorel

set_option autoImplicit false

namespace Foundations.Measure.Measure.Disintegration

open Foundations.Real

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {parameter : Space beta}

/-- Construct a disintegration for a joint measure whose conditioned space is
standard Borel and whose second marginal is sigma-finite. -/
@[expose] public noncomputable def ofStandardBorel
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SigmaFinite (secondMarginal joint)) : Disintegration joint :=
  comap joint presentation.embedding finite
    (ofUnit (joint.map (fun value => (presentation.embedding.function value.1, value.2))
      (Space.product_map presentation.embedding.measurable (MeasurableMap.identity parameter)))
      (by
        rw [secondMarginal_map_first joint presentation.embedding.function presentation.embedding.measurable]
        exact finite))

/-- Every conditional fiber of the raw standard-Borel disintegration has mass at
most one. -/
public theorem ofStandardBorel_univ_le_one
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SigmaFinite (secondMarginal joint)) (input : beta) :
    ENNReal.le ((ofStandardBorel joint presentation finite).conditional input Set.univ) ENNReal.one := by
  change ENNReal.le ((UnitDisintegration.conditional _ _).comap presentation.embedding input Set.univ) _
  rw [Kernel.comap_apply_univ,
    ← (UnitDisintegration.conditional_isProbability _ _ input).univ_eq_one]
  exact (UnitDisintegration.conditional _ _ input).mono (Set.subset_univ _)

/-- The conditional kernel of the raw standard-Borel disintegration is uniformly
finite with bound one. -/
public theorem ofStandardBorel_isFinite
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SigmaFinite (secondMarginal joint)) :
    Kernel.IsFinite (ofStandardBorel joint presentation finite).conditional :=
  ⟨⟨ENNReal.one, True.intro, ofStandardBorel_univ_le_one joint presentation finite⟩⟩

/-- Construct an everywhere-probability disintegration for a standard-Borel
conditioned space from a sigma-finite second marginal and an explicit fallback
point. -/
@[expose] public noncomputable def ofStandardBorelProbability
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SigmaFinite (secondMarginal joint)) (fallback : alpha) : Disintegration joint :=
  (ofStandardBorel joint presentation finite).probabilityVersion
    ((ofStandardBorel joint presentation finite).isProbability_ae finite) fallback

/-- Every conditional fiber of the repaired standard-Borel disintegration is a
probability measure. -/
public theorem ofStandardBorelProbability_isProbability
    (joint : Measure (Space.product source parameter)) (presentation : StandardBorel source)
    (finite : SigmaFinite (secondMarginal joint)) (fallback : alpha) (input : beta) :
    IsProbability ((ofStandardBorelProbability joint presentation finite fallback).conditional input) :=
  probabilityVersion_isProbability _ _ _ _

end Foundations.Measure.Measure.Disintegration
