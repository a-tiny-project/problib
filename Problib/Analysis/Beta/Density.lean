module

public import Problib.Analysis.Gamma.Beta
public import Problib.Measure.Kernel.Density.Normalized
public import Problib.Measure.Additive.Comap

/-! The Beta family on the unit interval.

The Beta weight is the Beta integrand at budget one,
`x^(first-1) (1-x)^(second-1)` on `0 < x < 1` and zero elsewhere
(`Beta.weight first second one`). Its integral against volume is Euler's Beta
integral (`family_normalizer`).

`Beta.law` is the normalized family of the weight against volume, so
`Beta.kernel` is measurable in the two shapes. Every law is a probability
measure. At positive shapes the law has density `weight/B(first, second)`
(`law_eq_withDensity`), so it gives the nonpositive half line no mass
(`law_nonpositive`).
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Beta

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The Beta weight at budget one is jointly measurable in the shapes and the
point. -/
public theorem unitWeight_jointly_measurable :
    ENNRealMeasurable (Space.product (Space.product borel borel) borel)
      (fun pair => weight pair.1.1 pair.1.2 one pair.2) :=
  (shapePower_jointly_measurable.comp (Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
      (Space.second_measurable _ _))).mul
    (shapePower_jointly_measurable.comp (Space.pair_measurable
      (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))
      (measurable_sub (MeasurableMap.constant _ borel one) (Space.second_measurable _ _))))

/-- The Beta family: the weight at budget one against volume. Its constant
fallback, the point zero, is arbitrary, because the family has no single
degenerate limit. -/
@[expose] public def family : Kernel.NormalizedFamily (Space.product borel borel) borel where
  reference := volume
  referenceFinite := volumeSFinite
  weight shapes value := weight shapes.1 shapes.2 one value
  weight_measurable := unitWeight_jointly_measurable
  fallback _ := zero
  fallback_measurable := MeasurableMap.constant _ borel zero

/-- The family's normalizer is Euler's Beta integral. -/
public theorem family_normalizer (first second : Carrier) :
    family.normalizer (first, second) = betaIntegral first second :=
  rfl

/-- A jointly measurable Beta kernel over all pairs of shapes. -/
@[expose] public def kernel : Kernel (Space.product borel borel) borel :=
  family.kernel

/-- The Beta law. -/
@[expose] public def law (first second : Carrier) : Measure borel :=
  family.law (first, second)

public theorem kernel_apply (first second : Carrier) : kernel (first, second) = law first second :=
  rfl

/-- Every Beta law is a probability measure. -/
public theorem law_isProbability (first second : Carrier) :
    Measure.IsProbability (law first second) :=
  family.law_isProbability (first, second)

/-- Euler's Beta function is positive at positive shapes. -/
public theorem beta_positive {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) : lt zero (beta first second) := by
  have integralPositive := betaIntegral_positive firstPositive secondPositive
  rw [← ofReal_beta firstPositive secondPositive, ← ENNReal.ofReal_zero] at integralPositive
  exact (ENNReal.ofReal_lt_ofReal_iff (le_refl zero) (ENNReal.toReal_nonnegative _)).mp
    integralPositive

/-- The Beta density against volume, `x^(first-1) (1-x)^(second-1)/B(first, second)`
on the unit interval. -/
@[expose] public def density (first second : Carrier) (value : Carrier) : ENNReal :=
  ENNReal.mul (ENNReal.ofReal (inverse (beta first second))) (weight first second one value)

public theorem density_measurable (first second : Carrier) :
    ENNRealMeasurable borel (density first second) :=
  (ENNRealMeasurable.constant _ _).mul (weight_measurable first second one)

/-- The Beta density is jointly measurable in the shapes and the point. -/
public theorem density_jointly_measurable :
    ENNRealMeasurable (Space.product (Space.product borel borel) borel)
      (fun triple => density triple.1.1 triple.1.2 triple.2) :=
  ((ofReal_measurable.comp (MeasurableMap.comp Problib.Measure.Real.inverse_measurable
      (MeasurableMap.comp toReal_measurable family.normalizer_measurable.measurableMap))).comp
    (Space.first_measurable _ _)).mul unitWeight_jointly_measurable

/-- The reciprocal of the Beta function cancels the family's normalizer. -/
public theorem inverse_mul_normalizer {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) :
    ENNReal.mul (ENNReal.ofReal (inverse (beta first second)))
      (family.normalizer (first, second)) = ENNReal.one := by
  rw [family_normalizer, ← ofReal_beta firstPositive secondPositive, ENNReal.mul_comm]
  exact ofReal_mul_ofReal_inverse (beta_positive firstPositive secondPositive)

/-- At positive shapes the law is volume weighted by the density. -/
public theorem law_eq_withDensity {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) :
    law first second = volume.withDensity (density first second) :=
  family.law_eq_of_scale (inverse_mul_normalizer firstPositive secondPositive) (fun _ => rfl)

/-- At positive shapes the law gives the nonpositive half line no mass. -/
public theorem law_nonpositive {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) : law first second (Iic zero) = ENNReal.zero := by
  rw [law_eq_withDensity firstPositive secondPositive,
    Measure.withDensity_apply _ _ (measurable_iic zero)]
  have pointwise : (volume.restrict (Iic zero)).AEEq (density first second)
      (fun _ => ENNReal.zero) :=
    (volume.ae_restrict_mem (measurable_iic zero)).mono fun value member => by
      show ENNReal.mul _ (ENNReal.mul (shapePower first value) _) = ENNReal.zero
      rw [shapePower_of_nonpositive first member, ENNReal.zero_mul, ENNReal.mul_zero]
  rw [lintegral_congr_ae pointwise, lintegral_zero]

/-- A Beta law read on the positive reals and carried back to the line is the
law itself. -/
public theorem law_comap_map {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) :
    ((law first second).comap (MeasurableEmbedding.subtype (Ioi zero) (measurable_ioi zero))).map
        (MeasurableEmbedding.subtype (Ioi zero) (measurable_ioi zero)).function
        (MeasurableEmbedding.subtype (Ioi zero) (measurable_ioi zero)).measurable =
      law first second := by
  apply Measure.map_comap_of_complement_null
  apply ENNReal.le_antisymm _ (ENNReal.zero_le _)
  rw [← law_nonpositive firstPositive secondPositive]
  exact (law first second).mono fun value outside =>
    not_lt_iff_le.mp fun positive => outside ⟨⟨value, positive⟩, rfl⟩

end

end Problib.Analysis.Beta
