module

public import Problib.Analysis.Gaussian.Moment
public import Problib.Analysis.Gaussian.RadialTail

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

private theorem reciprocal_coefficient (variance : Carrier) (positive : lt zero variance) :
    inverse (mul (selection.ofRat 2) (inverse (mul (selection.ofRat 2) variance))) = variance := by
  have tn := (positive_iff_nonnegative_and_nonzero.mp ofRat_two_positive).2
  have vn := (positive_iff_nonnegative_and_nonzero.mp positive).2
  have pn := (positive_iff_nonnegative_and_nonzero.mp (mul_positive ofRat_two_positive positive)).2
  have coefficient : mul (selection.ofRat 2) (inverse (mul (selection.ofRat 2) variance)) = inverse variance := by
    apply mul_right_cancel_of_nonzero (factor := variance) vn
    rw [inverse_mul_cancel vn, mul_assoc, mul_comm (inverse (mul (selection.ofRat 2) variance)),
      ← mul_assoc, mul_inverse_cancel pn]
  rw [coefficient, inverse_inverse]

/-- The variance is the evaluated centered second moment, before finite-real projection. -/
public theorem centered_second_moment (mean variance : Carrier) (positive : lt zero variance) :
    lintegral (law mean variance) (fun value => ENNReal.ofReal (mul (sub value mean) (sub value mean))) =
      ENNReal.ofReal variance := by
  let coefficient := inverse (mul (selection.ofRat 2) variance)
  let scale := ENNReal.ofReal (inverse (normalizer variance).toReal)
  have cp : lt zero coefficient := inverse_of_positive_positive (mul_positive ofRat_two_positive positive)
  have squareMeasurable : ENNRealMeasurable borel (fun value => ENNReal.ofReal (mul value value)) :=
    ofReal_measurable.comp (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel))
  have densityFactor (value : Carrier) : ENNReal.finite (density zero variance value) =
      ENNReal.mul scale (bell coefficient value) := by
    have formula := density_product zero variance value
    simp only [sub_eq_add_neg, neg_zero, add_zero, div_eq_mul_inverse] at formula
    exact formula.trans (congrArg (ENNReal.mul scale)
      (congrArg (fun value => ENNReal.ofReal (exp (neg value))) (mul_comm _ _)))
  have normalized : ENNReal.mul scale (lintegral volume (bell coefficient)) = ENNReal.one := by
    have mass := density_integral zero variance positive
    simp only [densityFactor] at mass
    rw [lintegral_smul _ _ (bell_measurable coefficient)] at mass
    exact mass
  rw [centered_integral mean variance squareMeasurable, law_integral zero variance squareMeasurable]
  have integrands : (fun value => ENNReal.mul (ENNReal.finite (density zero variance value))
      (ENNReal.ofReal (mul value value))) =
      (fun value => ENNReal.mul scale (ENNReal.mul (ENNReal.ofReal (mul value value)) (bell coefficient value))) := by
    funext value
    rw [densityFactor, ENNReal.mul_assoc, ENNReal.mul_comm (bell coefficient value)]
  rw [integrands, lintegral_smul _ _ (squareMeasurable.mul (bell_measurable coefficient)),
    second_weighted_integral coefficient cp]
  have scalar : inverse (mul (selection.ofRat 2) coefficient) = variance := reciprocal_coefficient variance positive
  rw [scalar, ← ENNReal.mul_assoc, ENNReal.mul_comm scale, ENNReal.mul_assoc, normalized, ENNReal.mul_one]

/-- The centered square has a finite integral certificate with zero negative part. -/
@[expose] public def varianceParts (mean variance : Carrier) (positive : lt zero variance) :
    IntegralParts (law mean variance) (fun value => mul (sub value mean) (sub value mean)) where
  positive := fun value => NNReal.ofReal (mul (sub value mean) (sub value mean))
  negative := fun _ => NNReal.zero
  positive_measurable := ofReal_measurable.comp (measurable_mul
    (measurable_sub (MeasurableMap.identity borel) (MeasurableMap.constant borel borel mean))
    (measurable_sub (MeasurableMap.identity borel) (MeasurableMap.constant borel borel mean)))
  negative_measurable := ENNRealMeasurable.constant borel ENNReal.zero
  decomposition := fun value => by
    rw [NNReal.toReal_ofReal (mul_self_nonnegative _), NNReal.toReal_zero]
    simp only [sub_eq_add_neg, neg_zero, add_zero]
  positiveMass := NNReal.ofReal variance
  negativeMass := NNReal.zero
  positive_integral := centered_second_moment mean variance positive
  negative_integral := lintegral_zero _

/-- The variance parameter is the finite signed expectation of the centered square. -/
public theorem variance_expectation (mean variance : Carrier) (positive : lt zero variance) :
    HasRealIntegral (law mean variance) (fun value => mul (sub value mean) (sub value mean)) variance := by
  refine ⟨varianceParts mean variance positive, ?_⟩
  change sub (NNReal.ofReal variance).toReal zero = variance
  rw [NNReal.toReal_ofReal positive.1, sub_eq_add_neg, neg_zero, add_zero]

private theorem square_add (left right : Carrier) :
    mul (add left right) (add left right) =
      add (add (mul left left) (mul (mul (selection.ofRat 2) right) left)) (mul right right) := by
  have twice (value : Carrier) : mul (selection.ofRat 2) value = add value value := by
    have two : selection.ofRat 2 = add one one := by
      rw [show (2 : Rat) = 1 + 1 from Rat.natCast_add 1 1, ofRat_add, ofRat_one]
    rw [two, mul_comm, mul_add, mul_one]
  have first : mul (add left right) left = add (mul left left) (mul right left) :=
    multiplicativeSelection.ring.add_mul _ _ _
  have second : mul (add left right) right = add (mul left right) (mul right right) :=
    multiplicativeSelection.ring.add_mul _ _ _
  rw [mul_add, first, second, mul_assoc (selection.ofRat 2) right left, twice, mul_comm right left]
  simp only [add_assoc]

/-- The raw square composes the finite centered square, centered first moment, and constant square. -/
@[expose] public def secondMomentParts (mean variance : Carrier) (positive : lt zero variance) :
    IntegralParts (law mean variance) (fun value => mul value value) :=
  (((varianceParts mean variance positive).addParts
      ((centeredParts mean variance positive).smul (mul (selection.ofRat 2) mean))).addParts
    (IntegralParts.const (law_isProbability mean variance positive) (mul mean mean))).congr (fun value => by
      have centered : add (sub value mean) mean = value := by
        rw [sub_eq_add_neg, add_assoc, add_comm (neg mean) mean, add_neg, add_zero]
      exact (square_add (sub value mean) mean).symm.trans (congrArg (fun value => mul value value) centered))

/-- The raw second moment is variance plus squared mean, with every signed part proved finite. -/
public theorem second_moment_expectation (mean variance : Carrier) (positive : lt zero variance) :
    HasRealIntegral (law mean variance) (fun value => mul value value) (add variance (mul mean mean)) := by
  refine ⟨secondMomentParts mean variance positive, ?_⟩
  change (((varianceParts mean variance positive).addParts
      ((centeredParts mean variance positive).smul (mul (selection.ofRat 2) mean))).addParts
    (IntegralParts.const (law_isProbability mean variance positive) (mul mean mean))).value = _
  have centered : (varianceParts mean variance positive).value = variance := by
    change sub (NNReal.ofReal variance).toReal zero = variance
    rw [NNReal.toReal_ofReal positive.1, sub_eq_add_neg, neg_zero, add_zero]
  have zeroProduct : mul (mul (selection.ofRat 2) mean) zero = zero := multiplicativeSelection.ring.mul_zero _
  rw [IntegralParts.addParts_value, IntegralParts.addParts_value, IntegralParts.smul_value,
    centeredParts_value, zeroProduct, add_zero, centered, IntegralParts.const_value]

end
end Problib.Analysis.Gaussian
