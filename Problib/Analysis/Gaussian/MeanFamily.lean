module

public import Problib.Analysis.Gaussian.Derivative
public import Problib.Analysis.Gaussian.Dominator
public import Problib.Analysis.Real.Leibniz

/-! Bounded tests weighted by the Gaussian density in its mean.

A bounded measurable test weighted by the Gaussian density is integrable
against volume at every mean, because it is integrable against the Gaussian law
and the law is volume with that density. Varying the mean gives a certified
integral family. Its secants are the test times the density's secants, so the
bound times the mean dominator dominates them, and the Leibniz rule
differentiates the family under the integral with the test times the density's
mean slope as the pointwise derivative.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

/-- A bounded measurable test is integrable against the Gaussian density at
every mean. -/
public theorem bounded_test_hasRealIntegral {mean variance bound : selection.Carrier}
    (positive : lt zero variance) {test : selection.Carrier → selection.Carrier}
    (measurable : MeasurableMap borel borel test)
    (bounded : ∀ value, le (abs (test value)) bound) :
    ∃ integral : selection.Carrier,
      HasRealIntegral volume (fun value => mul (test value) (density mean variance value).toReal)
        integral := by
  have probability := law_isProbability mean variance positive
  have constantFinite : ENNReal.Finite
      (lintegral (law mean variance) (fun _ => ENNReal.ofReal bound)) := by
    rw [lintegral_const, probability.univ_eq_one, ENNReal.mul_one]
    exact ENNReal.ofReal_finite bound
  have positiveFinite : ENNReal.Finite
      (lintegral (law mean variance) (fun value => ENNReal.ofReal (test value))) := by
    refine ENNReal.finite_of_le (lintegral_mono _ fun value => ?_) constantFinite
    exact ENNReal.ofReal_monotone (abs_le.mp (bounded value)).2
  have negativeFinite : ENNReal.Finite
      (lintegral (law mean variance) (fun value => ENNReal.ofReal (neg (test value)))) := by
    refine ENNReal.finite_of_le (lintegral_mono _ fun value => ?_) constantFinite
    have flipped := neg_le_neg_iff.mpr (abs_le.mp (bounded value)).1
    rw [neg_neg] at flipped
    exact ENNReal.ofReal_monotone flipped
  have lawIntegral : HasRealIntegral (law mean variance) test
      (IntegralParts.canonical measurable positiveFinite negativeFinite).value :=
    ⟨IntegralParts.canonical measurable positiveFinite negativeFinite, rfl⟩
  exact ⟨_, HasRealIntegral.of_withDensity (measure := volume)
    (density := fun value => density mean variance value)
    (density_measurable_slice mean variance) lawIntegral⟩

/-- A bounded measurable test weighted by the Gaussian density, as a certified
integral family in the mean. -/
@[expose] public def meanFamily (variance bound : selection.Carrier) (positive : lt zero variance)
    (test : selection.Carrier → selection.Carrier) (measurable : MeasurableMap borel borel test)
    (bounded : ∀ value, le (abs (test value)) bound) : IntegralFamily volume where
  integrand := fun mean value => mul (test value) (density mean variance value).toReal
  value := fun mean => Classical.choose (bounded_test_hasRealIntegral (mean := mean) positive
    measurable bounded)
  certified := fun mean => Classical.choose_spec (bounded_test_hasRealIntegral (mean := mean)
    positive measurable bounded)

/-- The test times the density's mean slope, the pointwise derivative of the
mean family. -/
@[expose] public def meanScore (mean variance : selection.Carrier)
    (test : selection.Carrier → selection.Carrier) (value : selection.Carrier) :
    selection.Carrier :=
  mul (test value) (mul (density mean variance value).toReal (div (sub value mean) variance))

/-- The bound times the mean dominator dominates every secant of the mean
family on the unit neighborhood of each mean. -/
public theorem meanFamily_dominated {variance bound : selection.Carrier}
    (positive : lt zero variance) {test : selection.Carrier → selection.Carrier}
    (measurable : MeasurableMap borel borel test)
    (bounded : ∀ value, le (abs (test value)) bound) (mean : selection.Carrier) :
    HasDominatedDifferenceQuotients (meanFamily variance bound positive test measurable bounded)
      mean := by
  have boundNonnegative : le zero bound := le_trans (abs_nonnegative (test zero)) (bounded zero)
  obtain ⟨dominatorValue, dominatorIntegral⟩ :=
    meanDominator_hasRealIntegral mean variance one positive
  refine ⟨one, fun value => mul bound (meanDominator mean variance one value),
    mul bound dominatorValue, one_positive, dominatorIntegral.smul bound,
    fun value => mul_nonnegative boundNonnegative
      (meanDominator_nonnegative mean variance one value positive (le_of_lt one_positive)),
    fun displacement nonzero small value => ?_⟩
  have factored : secant (fun step => mul (test value) (density step variance value).toReal)
      mean displacement =
      mul (test value) (secant (fun step => (density step variance value).toReal)
        mean displacement) := by
    rw [secant, secant, ← mul_sub, mul_div_assoc]
  show le (abs (secant (fun step => mul (test value) (density step variance value).toReal)
    mean displacement)) _
  rw [factored, abs_mul]
  exact le_trans (mul_le_mul_nonnegative_right (bounded value) (abs_nonnegative _))
    (mul_le_mul_nonnegative_left
      (mean_secant_le_dominator mean variance one value displacement positive nonzero small)
      boundNonnegative)

/-- The mean family differentiates under the integral sign at every mean, with
the test times the density's mean slope as the pointwise derivative. -/
public theorem meanFamily_differentiatesUnderIntegral {variance bound : selection.Carrier}
    (positive : lt zero variance) {test : selection.Carrier → selection.Carrier}
    (measurable : MeasurableMap borel borel test)
    (bounded : ∀ value, le (abs (test value)) bound) (mean : selection.Carrier) :
    ∃ derivative : selection.Carrier,
      DifferentiatesUnderIntegral (meanFamily variance bound positive test measurable bounded)
        mean (meanScore mean variance test) derivative := by
  have centered : MeasurableMap borel borel (fun value => sub value mean) :=
    measurable_sub (MeasurableMap.identity borel) (MeasurableMap.constant borel borel mean)
  have densityMeasurable : MeasurableMap borel borel
      (fun value => (density mean variance value).toReal) := by
    have formula : MeasurableMap borel borel (fun value => div (exp (neg (div
        (mul (sub value mean) (sub value mean)) (mul (selection.ofRat 2) variance))))
        (normalizer variance).toReal) :=
      measurable_div (MeasurableMap.comp exp_measurable (MeasurableMap.comp neg_measurable
        (measurable_div (measurable_mul centered centered)
          (MeasurableMap.constant _ borel _))))
        (MeasurableMap.constant _ borel _)
    have equal : (fun value => (density mean variance value).toReal) =
        (fun value => div (exp (neg (div (mul (sub value mean) (sub value mean))
          (mul (selection.ofRat 2) variance)))) (normalizer variance).toReal) :=
      funext fun value => density_toReal mean variance value
    rw [equal]
    intro set measurableSet
    exact formula measurableSet
  have scoreMeasurable : MeasurableMap borel borel (meanScore mean variance test) :=
    measurable_mul measurable (measurable_mul densityMeasurable
      (measurable_div centered (MeasurableMap.constant _ borel _)))
  exact differentiatesUnderIntegral_of_dominated
    (meanFamily_dominated positive measurable bounded mean)
    (fun value => hasDerivative_smul (test value)
      (hasDerivative_density_mean mean variance value positive))
    scoreMeasurable

end

end Problib.Analysis.Gaussian
