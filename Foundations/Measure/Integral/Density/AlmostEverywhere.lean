module

public import Foundations.Measure.Integral.Density.Basic
public import Foundations.Measure.Additive.AbsoluteContinuity
public import Foundations.Measure.Integral.Lebesgue.AlmostEverywhere

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha} {measure : Measure space}

public theorem withDensity_mono_ae {left right : alpha → ENNReal}
    (included : measure.AE (fun value => ENNReal.le (left value) (right value)))
    (set : Set alpha) :
    ENNReal.le ((measure.withDensity left) set) ((measure.withDensity right) set) := by
  apply le_of_measurable_le
  intro region regionMeasurable
  rw [measure.withDensity_apply left regionMeasurable,
    measure.withDensity_apply right regionMeasurable]
  exact lintegral_mono_ae (included.restrict region)

/-- Almost-everywhere equal densities produce identical density-weighted
measures. -/
public theorem withDensity_congr_ae {left right : alpha → ENNReal}
    (equal : measure.AEEq left right) :
    measure.withDensity left = measure.withDensity right := by
  apply withDensity_ext
  intro set _
  exact lintegral_congr_ae (equal.restrict set)

public theorem NullSet.withDensity {set : Set alpha}
    (nullSet : measure.NullSet set) (density : alpha → ENNReal) :
    (measure.withDensity density).NullSet set := by
  rcases nullSet.exists_measurable_superset with
    ⟨superset, measurable, included, nullSuperset⟩
  have weightedNull : (measure.withDensity density).NullSet superset := by
    rw [NullSet, measure.withDensity_apply density measurable,
      measure.restrict_eq_zero_of_null nullSuperset, lintegral_zero_measure]
  exact weightedNull.mono included

public theorem AE.withDensity {predicate : alpha → Prop}
    (holds : measure.AE predicate) (density : alpha → ENNReal) :
    (measure.withDensity density).AE predicate :=
  NullSet.withDensity holds density

/-- A density-weighted measure is absolutely continuous with respect to the base
measure. -/
public theorem absolutelyContinuous_withDensity (measure : Measure space)
    (density : alpha → ENNReal) :
    AbsolutelyContinuous (measure.withDensity density) measure := by
  intro set _ nullSet
  exact NullSet.withDensity nullSet density

/-- Any measure equipped with a density reconstruction certificate is
absolutely continuous with respect to the reference measure. -/
public theorem IsDensity.absolutelyContinuous {target reference : Measure space}
    {density : alpha → ENNReal} (reconstruct : IsDensity target reference density) :
    AbsolutelyContinuous target reference := by
  rw [reconstruct.eq_withDensity]
  exact absolutelyContinuous_withDensity reference density

end Foundations.Measure.Measure
