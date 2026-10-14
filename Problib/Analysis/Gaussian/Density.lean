module

public import Problib.Analysis.Gaussian.Integral
public import Problib.Measure.Kernel.Density.Normalized
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Real.Lebesgue

/-! Gaussian densities with variance as the second parameter.

The formula is totalized on all real parameters. Its probability interpretation
requires positive variance. The construction uses the proved Gaussian integral,
translation of volume, and finite positive cancellation. It supplies no numeric
implementation or executable sampler.

The law is the normalized family of the weight `exp(-(x-μ)²/(2v))` against
volume (`family`). At positive variance the weight integrates to the
normalizer `sqrt(2πv)`, and the law has the closed-form density
(`law_eq_withDensity`). At zero variance the weight is one everywhere and its
integral is infinite. The family's fallback is the mean, so the law there is
the Dirac measure at the mean (`law_zero_variance`), the weak limit of the
Gaussian laws as the variance shrinks to zero.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The density's normalizing denominator, sqrt(2*pi*variance). -/
@[expose] public def normalizer (variance : Carrier) : NNReal :=
  sqrt (NNReal.ofReal (mul (mul (selection.ofRat 2) pi) variance))

/-- The Gaussian density. The second argument is variance, not standard deviation. -/
@[expose] public def density (mean variance value : Carrier) : NNReal :=
  NNReal.ofReal (div
    (exp (neg (div (mul (sub value mean) (sub value mean))
      (mul (selection.ofRat 2) variance))))
    (normalizer variance).toReal)

public theorem normalizer_positive (variance : Carrier) (positive : lt zero variance) :
    NNReal.lt NNReal.zero (normalizer variance) := by
  apply sqrt_positive
  change lt zero (NNReal.toReal (NNReal.ofReal _))
  have h := mul_positive (mul_positive ofRat_two_positive pi_positive) positive
  rw [NNReal.toReal_ofReal h.1]
  exact h

/-- Projection to the real carrier gives the untruncated density formula. -/
public theorem density_toReal (mean variance value : Carrier) :
    (density mean variance value).toReal =
      div (exp (neg (div (mul (sub value mean) (sub value mean))
        (mul (selection.ofRat 2) variance)))) (normalizer variance).toReal :=
  NNReal.toReal_ofReal (div_nonnegative (exp_positive _).1 (normalizer variance).property)

/-- The totalized formula is jointly measurable, even outside its probability domain. -/
public theorem density_measurable :
    ENNRealMeasurable (Space.product (Space.product borel borel) borel)
      (fun p => ENNReal.finite (density p.1.1 p.1.2 p.2)) := by
  have root : MeasurableMap borel borel (fun x => (sqrt (NNReal.ofReal x)).toReal) :=
    monotone_measurable (fun _ _ h => sqrt_monotone (NNReal.ofReal_monotone h))
  have variance : MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => p.1.2) :=
    MeasurableMap.comp (Space.second_measurable borel borel) (Space.first_measurable _ _)
  have denominator : MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => (normalizer p.1.2).toReal) := MeasurableMap.comp root
    (measurable_mul (MeasurableMap.constant _ borel (mul (selection.ofRat 2) pi)) variance)
  exact ofReal_measurable.comp
    (measurable_div (MeasurableMap.comp exp_measurable gaussian_exponent_measurable) denominator)

public theorem density_measurable_slice (mean variance : Carrier) :
    ENNRealMeasurable borel (fun x => ENNReal.finite (density mean variance x)) :=
  Kernel.jointly_measurable_slice (source := Space.product borel borel) (target := borel)
    (density := fun p x => ENNReal.finite (density p.1 p.2 x)) density_measurable (mean, variance)

public theorem density_positive (mean variance : Carrier) (positive : lt zero variance)
    (value : Carrier) : lt zero (density mean variance value).toReal := by
  rw [density_toReal]
  exact div_positive (exp_positive _) (normalizer_positive variance positive)

/-- A bound independent of the mean and queried value, at each positive variance. -/
public theorem density_bound (variance : Carrier) (positive : lt zero variance)
    (mean value : Carrier) :
    NNReal.le (density mean variance value)
      (NNReal.ofReal (inverse (normalizer variance).toReal)) := by
  have denominator : le zero (normalizer variance).toReal := (normalizer variance).property
  have nonnegative := div_nonnegative (mul_self_nonnegative (sub value mean))
    (mul_positive ofRat_two_positive positive).1
  have bound := exp_monotone (neg_le_neg_iff.mpr nonnegative)
  rw [neg_zero, exp_zero] at bound
  change le (density mean variance value).toReal (NNReal.toReal (NNReal.ofReal _))
  rw [density_toReal, NNReal.toReal_ofReal (inverse_nonnegative denominator),
    div_eq_mul_inverse]
  simpa only [mul_comm one, mul_one] using
    mul_le_mul_nonnegative_right bound (inverse_nonnegative denominator)

/-- Factor the normalized density into its reciprocal normalizer and exponential. -/
public theorem density_product (mean variance value : Carrier) :
    ENNReal.finite (density mean variance value) =
      ENNReal.mul (ENNReal.ofReal (inverse (normalizer variance).toReal))
        (ENNReal.ofReal (exp (neg (div (mul (sub value mean) (sub value mean))
          (mul (selection.ofRat 2) variance))))) := by
  have denominator : le zero (normalizer variance).toReal := (normalizer variance).property
  change ENNReal.ofReal _ = _
  rw [div_eq_mul_inverse, mul_comm,
    ofReal_mul (inverse_nonnegative denominator) (exp_positive _).1]

/-- The centered, unnormalized Gaussian integrates to its normalizing denominator. -/
public theorem unnormalized_integral (mean variance : Carrier) (positive : lt zero variance) :
    lintegral volume (fun x => ENNReal.ofReal
      (exp (neg (div (mul (sub x mean) (sub x mean)) (mul (selection.ofRat 2) variance))))) =
      ENNReal.finite (normalizer variance) := by
  let coefficient := inverse (mul (selection.ofRat 2) variance)
  have cp : lt zero coefficient := inverse_of_positive_positive (mul_positive ofRat_two_positive positive)
  have measurable : ENNRealMeasurable borel
      (fun x => ENNReal.ofReal (exp (neg (mul coefficient (mul x x))))) :=
    ofReal_measurable.comp (MeasurableMap.comp exp_measurable
      (MeasurableMap.comp neg_measurable
        (measurable_mul (MeasurableMap.constant _ borel coefficient)
          (measurable_mul (MeasurableMap.identity _) (MeasurableMap.identity _)))))
  calc
    _ = lintegral volume (fun x => ENNReal.ofReal
        (exp (neg (mul coefficient (mul (add (neg mean) x) (add (neg mean) x)))))) := by
      apply lintegral_congr
      intro x
      rw [sub_eq_add_neg, add_comm x, div_eq_mul_inverse, mul_comm]
    _ = lintegral volume (fun x => ENNReal.ofReal
        (exp (neg (mul coefficient (mul x x))))) :=
      lintegral_volume_translate (neg mean) measurable
    _ = ENNReal.finite (sqrt (NNReal.ofReal (div pi coefficient))) :=
      gaussian_integral coefficient cp
    _ = ENNReal.finite (normalizer variance) := by
      have algebra : div pi coefficient = mul (mul (selection.ofRat 2) pi) variance := by
        change div pi (inverse (mul (selection.ofRat 2) variance)) = _
        rw [div_eq_mul_inverse, inverse_inverse, ← mul_assoc, mul_comm pi]
      rw [algebra]
      rfl

/-- The unnormalized Gaussian weight `exp(-(x-μ)²/(2v))`. -/
@[expose] public def weight (mean variance value : Carrier) : ENNReal :=
  ENNReal.ofReal (exp (neg (div (mul (sub value mean) (sub value mean))
    (mul (selection.ofRat 2) variance))))

public theorem weight_measurable :
    ENNRealMeasurable (Space.product (Space.product borel borel) borel)
      (fun p => weight p.1.1 p.1.2 p.2) :=
  ofReal_measurable.comp (MeasurableMap.comp exp_measurable gaussian_exponent_measurable)

/-- The Gaussian family: the weight against volume. Its fallback is the mean, the
degenerate Gaussian. -/
@[expose] public def family : Kernel.NormalizedFamily (Space.product borel borel) borel where
  reference := volume
  referenceFinite := volumeSFinite
  weight parameters value := weight parameters.1 parameters.2 value
  weight_measurable := weight_measurable
  fallback parameters := parameters.1
  fallback_measurable := Space.first_measurable borel borel

/-- At positive variance the family's normalizer is `sqrt(2πv)`. -/
public theorem family_normalizer (mean variance : Carrier) (positive : lt zero variance) :
    family.normalizer (mean, variance) = ENNReal.finite (normalizer variance) :=
  unnormalized_integral mean variance positive

private theorem scale_cancel (mean variance : Carrier) (positive : lt zero variance) :
    ENNReal.mul (ENNReal.ofReal (inverse (normalizer variance).toReal))
      (family.normalizer (mean, variance)) = ENNReal.one := by
  rw [family_normalizer mean variance positive]
  have root := normalizer_positive variance positive
  change ENNReal.finite (NNReal.mul (NNReal.ofReal (inverse (normalizer variance).toReal))
    (normalizer variance)) = ENNReal.finite NNReal.one
  apply congrArg ENNReal.finite
  apply NNReal.ext
  rw [NNReal.toReal_mul, NNReal.toReal_ofReal (inverse_of_positive_positive root).1]
  exact inverse_mul_cancel (positive_iff_nonnegative_and_nonzero.mp root).2

/-- A jointly measurable Gaussian kernel over all mean/variance pairs. Every
fiber is a probability measure, the Gaussian law at positive variance. -/
@[expose] public def kernel : Kernel (Space.product borel borel) borel :=
  family.kernel

/-- The Gaussian law. -/
@[expose] public def law (mean variance : Carrier) : Measure borel :=
  family.law (mean, variance)

public theorem kernel_apply (mean variance : Carrier) : kernel (mean, variance) = law mean variance :=
  rfl

/-- Every Gaussian law is a probability measure. -/
public theorem law_isProbability (mean variance : Carrier) :
    Measure.IsProbability (law mean variance) :=
  family.law_isProbability (mean, variance)

/-- At positive variance the law is volume weighted by the density. -/
public theorem law_eq_withDensity (mean variance : Carrier) (positive : lt zero variance) :
    law mean variance = volume.withDensity (fun x => ENNReal.finite (density mean variance x)) :=
  family.law_eq_of_scale (scale_cancel mean variance positive)
    (fun value => density_product mean variance value)

public theorem law_apply (mean variance : Carrier) (positive : lt zero variance)
    {region : Set Carrier} (measurable : borel.Measurable region) :
    law mean variance region = lintegral (volume.restrict region)
      (fun x => ENNReal.finite (density mean variance x)) := by
  rw [law_eq_withDensity mean variance positive]
  exact volume.withDensity_apply _ measurable

/-- Positive variance makes the density's whole-line integral exactly one. -/
public theorem density_integral (mean variance : Carrier) (positive : lt zero variance) :
    lintegral volume (fun x => ENNReal.finite (density mean variance x)) = ENNReal.one := by
  have total := (law_isProbability mean variance).univ_eq_one
  rwa [law_apply mean variance positive borel.univ, volume.restrict_univ] at total

/-- Integration against the law agrees with weighting by the explicit density. -/
public theorem law_integral (mean variance : Carrier) (positive : lt zero variance)
    {integrand : Carrier → ENNReal} (measurable : ENNRealMeasurable borel integrand) :
    lintegral (law mean variance) integrand = lintegral volume
      (fun x => ENNReal.mul (ENNReal.finite (density mean variance x)) (integrand x)) := by
  rw [law_eq_withDensity mean variance positive]
  exact lintegral_withDensity volume (density_measurable_slice mean variance) measurable

/-- The totalized density is zero at zero variance, not a Dirac density. -/
public theorem density_zero_variance (mean value : Carrier) :
    density mean zero value = NNReal.zero := by
  have zeroDenominator : mul (mul (selection.ofRat 2) pi) zero = zero :=
    multiplicativeSelection.ring.mul_zero _
  unfold density normalizer
  rw [zeroDenominator, NNReal.ofReal_zero, sqrt_zero]
  change NNReal.ofReal (div _ zero) = NNReal.zero
  rw [div_zero, NNReal.ofReal_zero]

public theorem density_integral_zero_variance (mean : Carrier) :
    lintegral volume (fun x => ENNReal.finite (density mean zero x)) = ENNReal.zero := by
  simp only [density_zero_variance]
  exact lintegral_zero volume

/-- At zero variance the weight is one everywhere, so its integral against
volume is infinite. -/
public theorem family_normalizer_zero_variance (mean : Carrier) :
    family.normalizer (mean, zero) = ENNReal.top := by
  have unit : weight mean zero = fun _ => ENNReal.one := by
    funext value
    unfold weight
    rw [mul_zero, div_zero, neg_zero, exp_zero, ENNReal.ofReal_one]
  show lintegral volume (weight mean zero) = ENNReal.top
  rw [unit, lintegral_const, volume_univ, ENNReal.one_mul]

/-- Normalization fails at zero variance, and the law there is the degenerate
Gaussian: the Dirac measure at the mean. -/
public theorem law_zero_variance (mean : Carrier) :
    law mean zero = Measure.dirac borel mean :=
  family.law_eq_dirac_of_top (family_normalizer_zero_variance mean)

end
end Problib.Analysis.Gaussian
