module

public import Problib.Analysis.Gaussian.Integral
public import Problib.Measure.Kernel.Density.Basic
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Kernel.RadonNikodym.Basic

/-! Gaussian densities with variance as the second parameter.

The formula is totalized on all real parameters. Its probability interpretation
requires positive variance. The construction uses the proved Gaussian integral,
translation of volume, and finite positive cancellation. It supplies no numeric
implementation or executable sampler.
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

/-- Positive variance makes the density's whole-line integral exactly one. -/
public theorem density_integral (mean variance : Carrier) (positive : lt zero variance) :
    lintegral volume (fun x => ENNReal.finite (density mean variance x)) = ENNReal.one := by
  have measurable : ENNRealMeasurable borel (fun x => ENNReal.ofReal
      (exp (neg (div (mul (sub x mean) (sub x mean)) (mul (selection.ofRat 2) variance))))) := by
    have centered : MeasurableMap borel borel (fun x => sub x mean) :=
      measurable_sub (MeasurableMap.identity borel)
      (MeasurableMap.constant borel borel mean)
    exact ofReal_measurable.comp (MeasurableMap.comp exp_measurable
      (MeasurableMap.comp neg_measurable
        (measurable_div (measurable_mul centered centered)
          (MeasurableMap.constant _ borel (mul (selection.ofRat 2) variance)))))
  simp only [density_product]
  rw [lintegral_smul _ _ measurable, unnormalized_integral mean variance positive]
  have root := normalizer_positive variance positive
  change ENNReal.finite (NNReal.mul (NNReal.ofReal (inverse (normalizer variance).toReal))
    (normalizer variance)) = ENNReal.finite NNReal.one
  apply congrArg ENNReal.finite
  apply NNReal.ext
  rw [NNReal.toReal_mul, NNReal.toReal_ofReal (inverse_of_positive_positive root).1]
  exact inverse_mul_cancel (positive_iff_nonnegative_and_nonzero.mp root).2

/-- The Gaussian measure as a density against the library's real volume. -/
@[expose] public def law (mean variance : Carrier) : Measure borel :=
  volume.withDensity (fun x => ENNReal.finite (density mean variance x))

public theorem law_apply (mean variance : Carrier) {region : Set Carrier}
    (measurable : borel.Measurable region) :
    law mean variance region = lintegral (volume.restrict region)
      (fun x => ENNReal.finite (density mean variance x)) :=
  volume.withDensity_apply _ measurable

/-- Positive variance supplies a proved probability law, with no analytic premise. -/
public theorem law_isProbability (mean variance : Carrier) (positive : lt zero variance) :
    Measure.IsProbability (law mean variance) := by
  constructor
  rw [law_apply mean variance borel.univ, volume.restrict_univ]
  exact density_integral mean variance positive

/-- A jointly measurable Gaussian kernel over all mean/variance pairs.
Its positive-variance fibers are probability measures. -/
@[expose] public def kernel : Kernel (Space.product borel borel) borel :=
  (Kernel.const (Space.product borel borel) volume).withDensity
    (Kernel.IsSFinite.const _ volumeSFinite)
    (fun parameters x => ENNReal.finite (density parameters.1 parameters.2 x)) density_measurable

public theorem kernel_apply (mean variance : Carrier) : kernel (mean, variance) = law mean variance :=
  rfl

/-- The explicit formula is a certified Radon-Nikodym density of the kernel. -/
@[expose] public def kernelDensity :
    Kernel.RadonNikodymDerivative kernel (Kernel.const (Space.product borel borel) volume) where
  density := fun parameters x => ENNReal.finite (density parameters.1 parameters.2 x)
  density_measurable := density_measurable
  reconstruct := fun _ => rfl

/-- Integration against the law agrees with weighting by the explicit density. -/
public theorem law_integral (mean variance : Carrier) {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral (law mean variance) integrand = lintegral volume
      (fun x => ENNReal.mul (ENNReal.finite (density mean variance x)) (integrand x)) :=
  lintegral_withDensity volume (density_measurable_slice mean variance) measurable

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

/-- Normalization cannot be asserted for every value of the variance parameter. -/
public theorem law_requires_positive (mean : Carrier) : ¬Measure.IsProbability (law mean zero) := by
  intro probability
  have mass := probability.univ_eq_one
  rw [law_apply mean zero borel.univ, volume.restrict_univ,
    density_integral_zero_variance] at mass
  exact ENNReal.one_ne_zero mass.symm

end
end Problib.Analysis.Gaussian
