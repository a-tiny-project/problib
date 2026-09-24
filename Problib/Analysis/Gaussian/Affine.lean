module

public import Problib.Analysis.Gaussian.Density

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- A positive standard deviation scales the Gaussian normalizer by that factor. -/
public theorem normalizer_square (scale : Carrier) (positive : lt zero scale) :
    (normalizer (mul scale scale)).toReal = mul scale (normalizer one).toReal := by
  let candidate : NNReal := ⟨mul scale (normalizer one).toReal,
    mul_nonnegative positive.1 (normalizer one).property⟩
  have constantPositive := mul_positive ofRat_two_positive pi_positive
  have targetPositive := mul_positive constantPositive (mul_positive positive positive)
  have baseSquare : mul (normalizer one).toReal (normalizer one).toReal =
      mul (selection.ofRat 2) pi := by
    have square := congrArg NNReal.toReal
      (sqrt_square (NNReal.ofReal (mul (mul (selection.ofRat 2) pi) one)))
    change mul (normalizer one).toReal (normalizer one).toReal = _ at square
    rw [mul_one] at square
    exact square.trans (NNReal.toReal_ofReal constantPositive.1)
  have square : NNReal.mul candidate candidate =
      NNReal.ofReal (mul (mul (selection.ofRat 2) pi) (mul scale scale)) := by
    apply NNReal.ext
    change mul (mul scale (normalizer one).toReal) (mul scale (normalizer one).toReal) = _
    rw [mul_mul_mul_comm, baseSquare, mul_comm, NNReal.toReal_ofReal targetPositive.1]
  exact (congrArg (fun value : NNReal => value.val) (sqrt_unique _ candidate square)).symm

private theorem exponent_affine (mean scale value : Carrier) (positive : lt zero scale) :
    div (mul (sub (add mean (mul scale value)) mean) (sub (add mean (mul scale value)) mean))
        (mul (selection.ofRat 2) (mul scale scale)) =
      div (mul (sub value zero) (sub value zero)) (mul (selection.ofRat 2) one) := by
  have centered : sub (add mean (mul scale value)) mean = mul scale value := by
    rw [sub_eq_add_neg, add_comm mean, add_assoc, add_neg, add_zero]
  rw [centered, sub_eq_add_neg, neg_zero, add_zero, mul_one, mul_mul_mul_comm]
  have scaleNonzero := (positive_iff_nonnegative_and_nonzero.mp positive).2
  have squaredNonzero : mul scale scale ≠ zero :=
    fun equal => (mul_eq_zero_iff.mp equal).elim scaleNonzero scaleNonzero
  have twoNonzero := (positive_iff_nonnegative_and_nonzero.mp ofRat_two_positive).2
  have denominatorNonzero : mul (selection.ofRat 2) (mul scale scale) ≠ zero :=
    fun equal => (mul_eq_zero_iff.mp equal).elim twoNonzero squaredNonzero
  apply mul_right_cancel_of_nonzero denominatorNonzero
  rw [div_eq_mul_inverse, mul_assoc, inverse_mul_cancel denominatorNonzero, mul_one,
    div_eq_mul_inverse, mul_assoc (mul value value),
    ← mul_assoc (inverse _) (selection.ofRat 2), inverse_mul_cancel twoNonzero,
    mul_comm one, mul_one, mul_comm]

/-- The Jacobian-scaled target density equals the standard density pointwise. -/
public theorem density_standard_affine (mean scale value : Carrier) (positive : lt zero scale) :
    ENNReal.finite (density zero one value) =
      ENNReal.mul (ENNReal.ofReal scale)
        (ENNReal.finite (density mean (mul scale scale) (add mean (mul scale value)))) := by
  have formula : (density zero one value).toReal =
      mul scale (density mean (mul scale scale) (add mean (mul scale value))).toReal := by
    rw [density_toReal, density_toReal, exponent_affine mean scale value positive,
      normalizer_square scale positive]
    have baseNonzero := (positive_iff_nonnegative_and_nonzero.mp
      (normalizer_positive one NNReal.one_positive)).2
    have scaleNonzero := (positive_iff_nonnegative_and_nonzero.mp positive).2
    have productNonzero : mul scale (normalizer one).toReal ≠ zero :=
      fun equal => (mul_eq_zero_iff.mp equal).elim scaleNonzero baseNonzero
    apply mul_right_cancel_of_nonzero productNonzero
    let numerator := exp (neg (div (mul (sub value zero) (sub value zero)) (mul (selection.ofRat 2) one)))
    change mul (div numerator (normalizer one).toReal) (mul scale (normalizer one).toReal) =
      mul (mul scale (div numerator (mul scale (normalizer one).toReal))) (mul scale (normalizer one).toReal)
    have cancel (n d : Carrier) (nonzero : d ≠ zero) : mul (div n d) d = n := by
      rw [div_eq_mul_inverse, mul_assoc, inverse_mul_cancel nonzero, mul_one]
    rw [mul_assoc scale, cancel numerator _ productNonzero,
      mul_comm scale (normalizer one).toReal, ← mul_assoc, cancel numerator _ baseNonzero, mul_comm]
  calc
    _ = ENNReal.ofReal (density zero one value).toReal := (ENNReal.ofReal_toReal_finite _).symm
    _ = ENNReal.ofReal (mul scale (density mean (mul scale scale) (add mean (mul scale value))).toReal) :=
      congrArg ENNReal.ofReal formula
    _ = ENNReal.mul (ENNReal.ofReal scale)
        (ENNReal.ofReal (density mean (mul scale scale) (add mean (mul scale value))).toReal) :=
      ofReal_mul positive.1 (density _ _ _).property
    _ = _ := congrArg (ENNReal.mul (ENNReal.ofReal scale)) (ENNReal.ofReal_toReal_finite _)

/-- Affine transport of a standard Gaussian has mean `mean` and variance `scale^2`. -/
public theorem law_standard_affine (mean scale : Carrier) (positive : lt zero scale) :
    (law zero one).map (fun value => add mean (mul scale value))
      (affine_measurable mean scale positive.1) = law mean (mul scale scale) := by
  apply Measure.ext
  intro region measurable
  rw [Measure.map_apply _ _ _ measurable, law_apply _ _ (affine_measurable mean scale positive.1 measurable),
    ← lintegral_indicator volume _ (affine_measurable mean scale positive.1 measurable)]
  have integrands : ennrealIndicator (Set.preimage (fun value => add mean (mul scale value)) region)
      (fun value => ENNReal.finite (density zero one value)) =
        (fun value => ENNReal.mul (ENNReal.ofReal scale)
          (ennrealIndicator region (fun point => ENNReal.finite (density mean (mul scale scale) point))
            (add mean (mul scale value)))) := by
    funext value
    classical
    by_cases member : region (add mean (mul scale value))
    · simp only [ennrealIndicator, ennrealPiecewise, Set.preimage, member, if_pos]
      exact density_standard_affine mean scale value positive
    · simp only [ennrealIndicator, ennrealPiecewise, Set.preimage, member, if_false, ENNReal.mul_zero]
  have indicatorMeasurable := ENNRealMeasurable.indicator measurable
    (density_measurable_slice mean (mul scale scale))
  have embeddedOne : ENNReal.ofReal one = ENNReal.one := ENNReal.ofReal_toReal_finite NNReal.one
  rw [integrands, lintegral_smul _ _ (indicatorMeasurable.comp (affine_measurable mean scale positive.1)),
    lintegral_volume_affine mean scale positive indicatorMeasurable, ← ENNReal.mul_assoc,
    ← ofReal_mul positive.1 (inverse_of_positive_positive positive).1,
    mul_inverse_cancel_of_positive positive, embeddedOne, ENNReal.one_mul,
    lintegral_indicator volume _ measurable, law_apply _ _ measurable]

/-- Every positive variance is reached by scaling a standard Gaussian by its nonnegative root. -/
public theorem law_standard_variance (mean variance : Carrier) (positive : lt zero variance) :
    (law zero one).map (fun value => add mean (mul (sqrt (NNReal.ofReal variance)).toReal value))
      (affine_measurable mean (sqrt (NNReal.ofReal variance)).toReal
        (sqrt (NNReal.ofReal variance)).property) = law mean variance := by
  have embedded : NNReal.lt NNReal.zero (NNReal.ofReal variance) := by
    change lt zero (NNReal.ofReal variance).toReal
    rw [NNReal.toReal_ofReal positive.1]
    exact positive
  have squared : mul (sqrt (NNReal.ofReal variance)).toReal (sqrt (NNReal.ofReal variance)).toReal = variance :=
    (congrArg NNReal.toReal (sqrt_square (NNReal.ofReal variance))).trans (NNReal.toReal_ofReal positive.1)
  exact (law_standard_affine mean _ (sqrt_positive _ embedded)).trans (congrArg (law mean) squared)

end
end Problib.Analysis.Gaussian
