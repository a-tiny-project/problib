module

public import Problib.Analysis.Gaussian.Density
public import Problib.Measure.Integral.Real

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

private theorem exponent_measurable (coefficient : Carrier) : ENNRealMeasurable borel
    (fun x => ENNReal.ofReal (exp (neg (mul coefficient (mul x x))))) :=
  ofReal_measurable.comp (MeasurableMap.comp exp_measurable
    (MeasurableMap.comp neg_measurable
      (measurable_mul (MeasurableMap.constant borel borel coefficient)
        (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel)))))

/-- The whole-line positive first moment of the unnormalized Gaussian.
The integrand vanishes on the nonpositive half line, so the proved radial
integral supplies its finite value. -/
public theorem positive_weighted_integral (coefficient : Carrier)
    (positive : lt zero coefficient) :
    lintegral volume (fun x => ENNReal.mul (ENNReal.ofReal x)
      (ENNReal.ofReal (exp (neg (mul coefficient (mul x x)))))) =
      ENNReal.ofReal (inverse (mul (selection.ofRat 2) coefficient)) := by
  have restricted : (fun x => ENNReal.mul (ENNReal.ofReal x)
      (ENNReal.ofReal (exp (neg (mul coefficient (mul x x)))))) =
      ennrealIndicator (Ioi zero) (fun x => ENNReal.ofReal
        (mul x (exp (neg (mul coefficient (mul x x)))))) := by
    funext x
    classical
    by_cases member : Ioi zero x
    · simp only [ennrealIndicator, ennrealPiecewise, if_pos member]
      exact (ofReal_mul member.1 (exp_positive _).1).symm
    · simp only [ennrealIndicator, ennrealPiecewise, if_neg member]
      rw [ENNReal.ofReal_eq_zero_iff.mpr (not_lt_iff_le.mp member), ENNReal.zero_mul]
  rw [restricted, lintegral_indicator volume _ (measurable_ioi zero)]
  exact radialIntegral_eq coefficient positive

/-- Both centered half moments of the normalized law will have this finite
value, variance / sqrt(2*pi*variance). -/
@[expose] public def halfMoment (variance : Carrier) : NNReal :=
  NNReal.div (NNReal.ofReal variance) (normalizer variance)

private theorem reciprocal_coefficient (variance : Carrier) (positive : lt zero variance) :
    inverse (mul (selection.ofRat 2) (inverse (mul (selection.ofRat 2) variance))) = variance := by
  have tn := (positive_iff_nonnegative_and_nonzero.mp ofRat_two_positive).2
  have vn := (positive_iff_nonnegative_and_nonzero.mp positive).2
  have pn := (positive_iff_nonnegative_and_nonzero.mp (mul_positive ofRat_two_positive positive)).2
  have coefficient : mul (selection.ofRat 2) (inverse (mul (selection.ofRat 2) variance)) =
      inverse variance := by
    apply mul_right_cancel_of_nonzero (factor := variance) vn
    rw [inverse_mul_cancel vn, mul_assoc, mul_comm (inverse (mul (selection.ofRat 2) variance)),
      ← mul_assoc, mul_inverse_cancel pn]
  rw [coefficient, inverse_inverse]

/-- The positive centered moment is finite and evaluated before any signed
subtraction is permitted. -/
public theorem positive_centered_moment (mean variance : Carrier) (positive : lt zero variance) :
    lintegral (law mean variance) (fun x => ENNReal.ofReal (sub x mean)) =
      ENNReal.finite (halfMoment variance) := by
  let coefficient := inverse (mul (selection.ofRat 2) variance)
  have cp : lt zero coefficient := inverse_of_positive_positive (mul_positive ofRat_two_positive positive)
  have centered : MeasurableMap borel borel (fun x => sub x mean) :=
    measurable_sub (MeasurableMap.identity borel) (MeasurableMap.constant borel borel mean)
  have weighted : ENNRealMeasurable borel (fun x => ENNReal.mul (ENNReal.ofReal x)
      (ENNReal.ofReal (exp (neg (mul coefficient (mul x x)))))) :=
    ofReal_measurable.mul (exponent_measurable coefficient)
  have shifted : ENNRealMeasurable borel (fun x => ENNReal.mul (ENNReal.ofReal (sub x mean))
      (ENNReal.ofReal (exp (neg (mul coefficient (mul (sub x mean) (sub x mean))))))) :=
    ENNRealMeasurable.comp
      (map := fun x => ENNReal.mul (ENNReal.ofReal x)
        (ENNReal.ofReal (exp (neg (mul coefficient (mul x x))))))
      (before := fun x => sub x mean) weighted centered
  rw [law_integral mean variance (ofReal_measurable.comp centered)]
  have integrand : (fun x => ENNReal.mul (ENNReal.finite (density mean variance x))
      (ENNReal.ofReal (sub x mean))) =
      (fun x => ENNReal.mul (ENNReal.ofReal (inverse (normalizer variance).toReal))
        (ENNReal.mul (ENNReal.ofReal (sub x mean))
          (ENNReal.ofReal (exp (neg (mul coefficient (mul (sub x mean) (sub x mean)))))))) := by
    funext x
    rw [density_product, ENNReal.mul_assoc, ENNReal.mul_comm _ (ENNReal.ofReal (sub x mean)),
      div_eq_mul_inverse, mul_comm (mul (sub x mean) (sub x mean))]
  rw [integrand, lintegral_smul _ _ shifted]
  have translate : lintegral volume (fun x => ENNReal.mul (ENNReal.ofReal (sub x mean))
      (ENNReal.ofReal (exp (neg (mul coefficient (mul (sub x mean) (sub x mean))))))) =
      lintegral volume (fun x => ENNReal.mul (ENNReal.ofReal x)
        (ENNReal.ofReal (exp (neg (mul coefficient (mul x x)))))) := by
    simpa only [sub_eq_add_neg, add_comm (neg mean)] using lintegral_volume_translate (neg mean) weighted
  rw [translate, positive_weighted_integral coefficient cp]
  change ENNReal.mul (ENNReal.ofReal (inverse (normalizer variance).toReal))
    (ENNReal.ofReal (inverse (mul (selection.ofRat 2)
      (inverse (mul (selection.ofRat 2) variance))))) = _
  rw [reciprocal_coefficient variance positive]
  change ENNReal.finite (NNReal.mul (NNReal.ofReal (inverse (normalizer variance).toReal))
    (NNReal.ofReal variance)) = ENNReal.finite (halfMoment variance)
  apply congrArg ENNReal.finite
  apply NNReal.ext
  have np : lt zero (normalizer variance).toReal := normalizer_positive variance positive
  rw [NNReal.toReal_mul, NNReal.toReal_ofReal (inverse_of_positive_positive np).1,
    NNReal.toReal_ofReal positive.1]
  change _ = (NNReal.div (NNReal.ofReal variance) (normalizer variance)).toReal
  rw [NNReal.toReal_div, NNReal.toReal_ofReal positive.1, div_eq_mul_inverse, mul_comm]

/-- Moving the mean translates every measurable nonnegative integrand. -/
public theorem centered_integral (mean variance : Carrier) {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral (law mean variance) (fun x => integrand (sub x mean)) =
      lintegral (law zero variance) integrand := by
  have centered : MeasurableMap borel borel (fun x => sub x mean) :=
    measurable_sub (MeasurableMap.identity borel) (MeasurableMap.constant borel borel mean)
  rw [law_integral mean variance (measurable.comp centered), law_integral zero variance measurable]
  have density_center (x : Carrier) : density mean variance x = density zero variance (sub x mean) := by
    simp only [density, sub_eq_add_neg, neg_zero, add_zero]
  simp only [density_center]
  have translated := lintegral_volume_translate (neg mean)
    ((density_measurable_slice zero variance).mul measurable)
  simpa only [sub_eq_add_neg, add_comm (neg mean)] using translated

/-- The zero-mean Gaussian is reflection invariant, before any moment is
projected to a finite signed real. -/
public theorem reflection_integral (variance : Carrier) {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral (law zero variance) (fun x => integrand (neg x)) =
      lintegral (law zero variance) integrand := by
  rw [law_integral zero variance (measurable.comp neg_measurable),
    law_integral zero variance measurable]
  have reflected (x : Carrier) : density zero variance (neg x) = density zero variance x := by
    have squares : mul (neg x) (neg x) = mul x x :=
      multiplicativeSelection.ring.neg_mul_neg x x
    simp only [density, sub_eq_add_neg, neg_zero, add_zero, squares]
  have invariant := lintegral_volume_neg ((density_measurable_slice zero variance).mul measurable)
  simpa only [reflected] using invariant

/-- The negative centered half has the same evaluated finite moment as the
positive half. Reflection is applied to the measure, not assumed of a sampler. -/
public theorem negative_centered_moment (mean variance : Carrier) (positive : lt zero variance) :
    lintegral (law mean variance) (fun x => ENNReal.ofReal (neg (sub x mean))) =
      ENNReal.finite (halfMoment variance) := by
  rw [centered_integral mean variance (ofReal_measurable.comp neg_measurable),
    reflection_integral variance ofReal_measurable]
  have positiveMoment := positive_centered_moment zero variance positive
  simpa only [sub_eq_add_neg, neg_zero, add_zero] using positiveMoment

/-- Absolute centered first moment, represented by the sum of positive and
negative parts. Finiteness follows from the evaluated halves. -/
public theorem absolute_centered_moment (mean variance : Carrier) (positive : lt zero variance) :
    lintegral (law mean variance) (fun x => ENNReal.add
      (ENNReal.ofReal (sub x mean)) (ENNReal.ofReal (neg (sub x mean)))) =
      ENNReal.finite (NNReal.add (halfMoment variance) (halfMoment variance)) := by
  have centered : MeasurableMap borel borel (fun x => sub x mean) :=
    measurable_sub (MeasurableMap.identity borel) (MeasurableMap.constant borel borel mean)
  rw [lintegral_add _ (ofReal_measurable.comp centered)
    (ofReal_measurable.comp (MeasurableMap.comp neg_measurable centered)),
    positive_centered_moment mean variance positive, negative_centered_moment mean variance positive]
  rfl

public theorem absolute_centered_moment_finite (mean variance : Carrier) (positive : lt zero variance) :
    ENNReal.Finite (lintegral (law mean variance) (fun x => ENNReal.add
      (ENNReal.ofReal (sub x mean)) (ENNReal.ofReal (neg (sub x mean))))) := by
  rw [absolute_centered_moment mean variance positive]
  trivial

/-- A finite signed integral certificate for the centered identity function. -/
@[expose] public def centeredParts (mean variance : Carrier) (positive : lt zero variance) :
    IntegralParts (law mean variance) (fun x => sub x mean) where
  positive := fun x => NNReal.ofReal (sub x mean)
  negative := fun x => NNReal.ofReal (neg (sub x mean))
  positive_measurable := ofReal_measurable.comp
    (measurable_sub (MeasurableMap.identity borel) (MeasurableMap.constant borel borel mean))
  negative_measurable := ofReal_measurable.comp (MeasurableMap.comp neg_measurable
    (measurable_sub (MeasurableMap.identity borel) (MeasurableMap.constant borel borel mean)))
  decomposition := fun x => IntegralParts.scalar_decomposition (sub x mean)
  positiveMass := halfMoment variance
  negativeMass := halfMoment variance
  positive_integral := positive_centered_moment mean variance positive
  negative_integral := negative_centered_moment mean variance positive

public theorem centeredParts_value (mean variance : Carrier) (positive : lt zero variance) :
    (centeredParts mean variance positive).value = zero := by
  change sub (halfMoment variance).toReal (halfMoment variance).toReal = zero
  rw [sub_eq_add_neg, add_neg]

/-- The centered expectation is zero, with finite positive and negative
integrals rather than a totalized infinity subtraction. -/
public theorem centered_expectation (mean variance : Carrier) (positive : lt zero variance) :
    HasRealIntegral (law mean variance) (fun x => sub x mean) zero :=
  ⟨centeredParts mean variance positive, centeredParts_value mean variance positive⟩

/-- The identity is its centered version plus the constant mean. Its finite
integral decomposition composes the two independently checked certificates. -/
@[expose] public def meanParts (mean variance : Carrier) (positive : lt zero variance) :
    IntegralParts (law mean variance) (fun x => x) :=
  ((centeredParts mean variance positive).addParts
    (IntegralParts.const (law_isProbability mean variance positive) mean)).congr (fun x => by
      rw [sub_eq_add_neg, add_assoc, add_comm (neg mean) mean, add_neg, add_zero])

/-- The normal distribution has the stated mean, with a proved finite signed
integral certificate for every strictly positive variance. -/
public theorem mean_expectation (mean variance : Carrier) (positive : lt zero variance) :
    HasRealIntegral (law mean variance) (fun x => x) mean := by
  refine ⟨meanParts mean variance positive, ?_⟩
  change ((centeredParts mean variance positive).addParts
    (IntegralParts.const (law_isProbability mean variance positive) mean)).value = mean
  rw [IntegralParts.addParts_value, centeredParts_value, IntegralParts.const_value,
    add_comm zero, add_zero]

end
end Problib.Analysis.Gaussian
