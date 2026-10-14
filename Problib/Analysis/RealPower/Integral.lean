module

public import Problib.Analysis.RealPower
public import Problib.Analysis.Exponential.Tail
import Problib.Measure.Real.IntervalIntegral

/-! The unit power integral by exponential substitution.

`y ↦ exp (-y)` carries the rate-one exponential law on the positive half line
to volume on `(0,1]`. The two measures agree on every lower ray, which the
exponential tail evaluates, so no derivative or primitive is used. Under that
substitution `x ^ (a-1) dx` becomes `exp (-a y) dy`, whose half-line integral
is `1/a`. Positive scaling then moves the unit interval to `(0,t]`.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Logarithm

noncomputable section

private theorem exponential_univ :
    ((volume.restrict (Ioi zero)).withDensity (Exponential.weight one)) Set.univ =
      ENNReal.one := by
  rw [Measure.withDensity_apply _ _ borel.univ, Measure.restrict_restrict _ _ borel.univ,
    Set.inter_univ_left, Exponential.integral one one_positive, inverse_one, ENNReal.ofReal_one]

private theorem exponential_ioi {threshold : Carrier} (nonnegative : le zero threshold) :
    ((volume.restrict (Ioi zero)).withDensity (Exponential.weight one)) (Ioi threshold) =
      Exponential.weight one threshold := by
  rw [Measure.withDensity_apply _ _ (measurable_ioi threshold),
    Measure.restrict_restrict _ _ (measurable_ioi threshold)]
  have same : Set.inter (Ioi threshold) (Ioi zero) = Ioi threshold :=
    Set.ext (fun _ => ⟨fun member => member.1,
      fun member => ⟨member, lt_of_le_of_lt nonnegative member⟩⟩)
  rw [same, Exponential.tail one threshold one_positive, inverse_one, ENNReal.ofReal_one,
    ENNReal.mul_one]

private theorem exponential_ioi_negative {threshold : Carrier} (negative : lt threshold zero) :
    ((volume.restrict (Ioi zero)).withDensity (Exponential.weight one)) (Ioi threshold) =
      ENNReal.one := by
  rw [Measure.withDensity_apply _ _ (measurable_ioi threshold),
    Measure.restrict_restrict _ _ (measurable_ioi threshold)]
  have same : Set.inter (Ioi threshold) (Ioi zero) = Ioi zero :=
    Set.ext (fun _ => ⟨fun member => member.2,
      fun member => ⟨lt_trans negative member, member⟩⟩)
  rw [same, Exponential.integral one one_positive, inverse_one, ENNReal.ofReal_one]

private theorem preimage_exp_neg_iio {upper : Carrier} (positive : lt zero upper) :
    Set.preimage (fun value => exp (neg value)) (Iio upper) =
      Ioi (neg (logIntegral upper)) := by
  apply Set.ext
  intro value
  change lt (exp (neg value)) upper ↔ lt (neg (logIntegral upper)) value
  rw [← not_le_iff_lt, ← not_le_iff_lt, exp_neg_sublevel upper value positive]

/-- `y ↦ exp (-y)` carries the rate-one exponential law on the positive half
line to volume on `(0,1]`. -/
public theorem map_exponential_exp_neg :
    ((volume.restrict (Ioi zero)).withDensity (Exponential.weight one)).map
        (fun value => exp (neg value)) (MeasurableMap.comp exp_measurable neg_measurable) =
      volume.restrict (Ioc zero one) := by
  classical
  have unitVolume : volume (Ioc zero one) = ENNReal.one := by
    rw [volume_ioc, sub_zero, ENNReal.ofReal_one]
  have mappedTotal :
      (((volume.restrict (Ioi zero)).withDensity (Exponential.weight one)).map
        (fun value => exp (neg value)) (MeasurableMap.comp exp_measurable neg_measurable))
          Set.univ = ENNReal.one := by
    rw [Measure.map_apply _ _ _ borel.univ]
    exact exponential_univ
  apply finite_measure_ext_iio
  · exact ⟨by rw [mappedTotal]; exact True.intro⟩
  · exact ⟨by rw [Measure.restrict_apply_univ, unitVolume]; exact True.intro⟩
  · rw [mappedTotal, Measure.restrict_apply_univ, unitVolume]
  · intro upper
    rw [Measure.map_apply _ _ _ (measurable_iio upper),
      Measure.restrict_apply _ _ (measurable_iio upper)]
    by_cases positive : lt zero upper
    · rw [preimage_exp_neg_iio positive]
      by_cases below : le upper one
      · have logNonpositive : le (logIntegral upper) zero := by
          have monotone := log_monotone upper one positive below
          rwa [log_one] at monotone
        rw [exponential_ioi (neg_nonnegative_iff.mpr logNonpositive)]
        have same : Set.inter (Iio upper) (Ioc zero one) = Ioo zero upper :=
          Set.ext (fun _ => ⟨fun member => ⟨member.2.1, member.1⟩,
            fun member => ⟨member.2, member.1, le_trans member.2.1 below⟩⟩)
        rw [same, volume_ioo, sub_zero]
        unfold Exponential.weight
        rw [one_mul, neg_neg, exp_log upper positive]
      · have above : lt one upper := not_le_iff_lt.mp below
        have logPositive : lt zero (logIntegral upper) := by
          have strict := log_strict one upper one_positive above
          rwa [log_one] at strict
        rw [exponential_ioi_negative (neg_negative_iff.mp logPositive)]
        have same : Set.inter (Iio upper) (Ioc zero one) = Ioc zero one :=
          Set.ext (fun _ => ⟨fun member => member.2,
            fun member => ⟨lt_of_le_of_lt member.2 above, member⟩⟩)
        rw [same, unitVolume]
    · have nonpositive : le upper zero := not_lt_iff_le.mp positive
      have emptyPreimage : Set.preimage (fun value => exp (neg value)) (Iio upper) =
          Set.empty :=
        Set.ext (fun value => ⟨fun member =>
          (exp_positive (neg value)).2 (le_trans member.1 nonpositive), False.elim⟩)
      have emptyInterval : Set.inter (Iio upper) (Ioc zero one) = Set.empty :=
        Set.ext (fun _ => ⟨fun member => member.2.1.2 (le_trans member.1.1 nonpositive),
          False.elim⟩)
      rw [emptyPreimage, emptyInterval, Measure.empty_apply, Measure.empty_apply]

/-- Substituting `x = exp (-y)` turns an integral over the unit interval into
an exponentially weighted integral over the positive half line. -/
public theorem lintegral_unit_interval_exp_neg {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral (volume.restrict (Ioc zero one)) integrand =
      lintegral (volume.restrict (Ioi zero))
        (fun value =>
          ENNReal.mul (Exponential.weight one value) (integrand (exp (neg value)))) := by
  rw [← map_exponential_exp_neg,
    lintegral_map _ _ (MeasurableMap.comp exp_measurable neg_measurable) measurable,
    lintegral_withDensity _ (Exponential.weight_measurable one)
      (measurable.comp (MeasurableMap.comp exp_measurable neg_measurable))]

/-- Under the substitution the power `x ^ (a-1)` and the Jacobian `exp (-y)`
combine into the rate-`a` exponential. -/
private theorem weight_mul_rpow (exponent value : Carrier) :
    ENNReal.mul (Exponential.weight one value)
        (ENNReal.ofReal (rpow (exp (neg value)) (sub exponent one))) =
      Exponential.weight exponent value := by
  unfold Exponential.weight
  rw [rpow_exp, ← ofReal_mul (exp_positive _).1 (exp_positive _).1, ← exp_add, mul_neg,
    sub_mul, ← neg_add, add_sub_cancel]

/-- `∫₀¹ x ^ (a-1) dx = 1/a` for every positive exponent `a`. -/
public theorem rpow_unit_integral (exponent : Carrier) (positive : lt zero exponent) :
    lintegral (volume.restrict (Ioc zero one))
        (fun value => ENNReal.ofReal (rpow value (sub exponent one))) =
      ENNReal.ofReal (inverse exponent) := by
  rw [lintegral_unit_interval_exp_neg (ofReal_measurable.comp (rpow_measurable (sub exponent one)))]
  exact (lintegral_congr _ (weight_mul_rpow exponent)).trans
    (Exponential.integral exponent positive)

/-- Positive scaling moves volume on the unit interval to `(0,bound]`. -/
private theorem map_unit_interval_scale {bound : Carrier} (positive : lt zero bound) :
    (volume.restrict (Ioc zero one)).map (mul bound) (scale_measurable bound positive.1) =
      Measure.smul (ENNReal.ofReal (inverse bound)) (volume.restrict (Ioc zero bound)) := by
  have mapped := Measure.map_restrict volume (mul bound) (scale_measurable bound positive.1)
    (measurable_ioc zero bound)
  rw [preimage_scale_ioc bound zero bound positive, mul_zero,
    inverse_mul_cancel (nonzero_of_positive positive), map_volume_scale bound positive,
    Measure.restrict_smul _ _ (measurable_ioc zero bound)] at mapped
  exact mapped

/-- `∫₀ᵗ x ^ (a-1) dx = t ^ a / a` for every positive exponent `a` and bound `t`. -/
public theorem rpow_interval_integral (exponent bound : Carrier) (positive : lt zero exponent)
    (boundPositive : lt zero bound) :
    lintegral (volume.restrict (Ioc zero bound))
        (fun value => ENNReal.ofReal (rpow value (sub exponent one))) =
      ENNReal.ofReal (div (rpow bound exponent) exponent) := by
  have integrandMeasurable : ENNRealMeasurable borel
      (fun value => ENNReal.ofReal (rpow value (sub exponent one))) :=
    ofReal_measurable.comp (rpow_measurable (sub exponent one))
  have scaled := lintegral_map (volume.restrict (Ioc zero one)) (mul bound)
    (scale_measurable bound boundPositive.1) integrandMeasurable
  rw [map_unit_interval_scale boundPositive, lintegral_smul_measure] at scaled
  have factored : lintegral (volume.restrict (Ioc zero one))
      (fun value => ENNReal.ofReal (rpow (mul bound value) (sub exponent one))) =
      ENNReal.mul (ENNReal.ofReal (rpow bound (sub exponent one)))
        (ENNReal.ofReal (inverse exponent)) := by
    have same := (volume.ae_restrict_mem (measurable_ioc zero one)).mono
      (fun value member =>
        show ENNReal.ofReal (rpow (mul bound value) (sub exponent one)) =
          ENNReal.mul (ENNReal.ofReal (rpow bound (sub exponent one)))
            (ENNReal.ofReal (rpow value (sub exponent one))) from by
          rw [mul_rpow boundPositive.1 member.1.1 (sub exponent one),
            ofReal_mul (rpow_nonnegative _ _) (rpow_nonnegative _ _)])
    rw [lintegral_congr_ae same, lintegral_smul _ _ integrandMeasurable,
      rpow_unit_integral exponent positive]
  have split : rpow bound exponent = mul bound (rpow bound (sub exponent one)) := by
    calc
      rpow bound exponent = rpow bound (add one (sub exponent one)) := by
        rw [add_sub_cancel]
      _ = mul (rpow bound one) (rpow bound (sub exponent one)) :=
        rpow_add boundPositive _ _
      _ = mul bound (rpow bound (sub exponent one)) := by
        rw [rpow_one boundPositive.1]
  have inverseNonnegative := (inverse_of_positive_positive positive).1
  calc
    lintegral (volume.restrict (Ioc zero bound))
        (fun value => ENNReal.ofReal (rpow value (sub exponent one))) =
        ENNReal.mul (ENNReal.mul (ENNReal.ofReal bound) (ENNReal.ofReal (inverse bound)))
          (lintegral (volume.restrict (Ioc zero bound))
            (fun value => ENNReal.ofReal (rpow value (sub exponent one)))) := by
      rw [ofReal_mul_ofReal_inverse boundPositive, ENNReal.one_mul]
    _ = ENNReal.mul (ENNReal.ofReal bound)
          (ENNReal.mul (ENNReal.ofReal (rpow bound (sub exponent one)))
            (ENNReal.ofReal (inverse exponent))) := by
      rw [ENNReal.mul_assoc, scaled, factored]
    _ = ENNReal.ofReal (div (rpow bound exponent) exponent) := by
      rw [← ofReal_mul (rpow_nonnegative _ _) inverseNonnegative,
        ← ofReal_mul boundPositive.1 (mul_nonnegative (rpow_nonnegative _ _) inverseNonnegative),
        div_eq_mul_inverse, split, mul_assoc]

/-- The unit integral diverges at exponent zero, where the integrand is `1/x`. -/
public theorem rpow_unit_integral_zero_eq_top :
    lintegral (volume.restrict (Ioc zero one))
        (fun value => ENNReal.ofReal (rpow value (sub zero one))) = ENNReal.top := by
  rw [lintegral_unit_interval_exp_neg (ofReal_measurable.comp (rpow_measurable (sub zero one)))]
  have constant (value : Carrier) :
      ENNReal.mul (Exponential.weight one value)
        (ENNReal.ofReal (rpow (exp (neg value)) (sub zero one))) = ENNReal.one := by
    rw [weight_mul_rpow zero value]
    unfold Exponential.weight
    rw [zero_mul, neg_zero, exp_zero, ENNReal.ofReal_one]
  rw [lintegral_congr _ constant, lintegral_const, Measure.restrict_apply_univ, ENNReal.one_mul]
  exact volume_ioi_zero

end
end Problib.Analysis
