module

public import Problib.Analysis.Gamma.Beta
public import Problib.Measure.Kernel.Density.Normalized
public import Problib.Measure.Integral.Density.Change

/-! Gamma densities with shape and rate parameters.

`density shape rate value` is `rate^shape value^(shape-1) e^(-rate value) /
Γ(shape)` on the positive half line and zero elsewhere. The formula is
totalized on all real parameters. Positive shape and rate make it a probability
density: positive scaling of volume turns the rate into the factor
`rate^shape`, which the numerator cancels. At rate zero the unnormalized mass is
infinite at every positive shape, and the totalized density is zero when either
parameter is zero. The construction supplies no sampler.

The law is the normalized family of the weight `x^(shape-1) e^(-rate x)` on the
positive half line against volume (`family`). At positive shape and rate its
normalizer is `Γ(shape)/rate^shape` and the law has the closed-form density
(`law_eq_withDensity`). At zero rate or zero shape the normalizer is infinite
and the law is the fallback point mass at one (`law_zero_rate`,
`law_zero_shape`). That fallback is arbitrary: the Gamma family has no single
degenerate limit.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Gamma

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The Gamma density with shape and rate. It is zero off the positive half
line. -/
@[expose] public def density (shape rate value : Carrier) : NNReal := by
  classical
  exact NNReal.ofReal (if lt zero value then
      div (mul (rpow rate shape) (mul (rpow value (sub shape one)) (exp (neg (mul rate value)))))
        (gamma shape)
    else zero)

public theorem density_of_positive (shape rate : Carrier) {value : Carrier}
    (positive : lt zero value) :
    density shape rate value = NNReal.ofReal (div (mul (rpow rate shape)
      (mul (rpow value (sub shape one)) (exp (neg (mul rate value))))) (gamma shape)) := by
  unfold density
  rw [ite_eq_left positive]

public theorem density_of_nonpositive (shape rate : Carrier) {value : Carrier}
    (nonpositive : le value zero) : density shape rate value = NNReal.zero := by
  unfold density
  rw [ite_eq_right (fun positive : lt zero value => positive.2 nonpositive), NNReal.ofReal_zero]

/-- The totalized formula is jointly measurable in shape, rate and value, even
outside its probability domain. -/
public theorem density_measurable :
    ENNRealMeasurable (Space.product (Space.product borel borel) borel)
      (fun p => ENNReal.finite (density p.1.1 p.1.2 p.2)) := by
  have shape : MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => p.1.1) :=
    MeasurableMap.comp (Space.first_measurable borel borel) (Space.first_measurable _ _)
  have rate : MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => p.1.2) :=
    MeasurableMap.comp (Space.second_measurable borel borel) (Space.first_measurable _ _)
  have value : MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => p.2) := Space.second_measurable _ _
  have scale : MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => rpow p.1.2 p.1.1) :=
    MeasurableMap.comp rpow_jointly_measurable (Space.pair_measurable rate shape)
  have power : MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => rpow p.2 (sub p.1.1 one)) :=
    MeasurableMap.comp rpow_jointly_measurable (Space.pair_measurable value
      (measurable_sub shape (MeasurableMap.constant _ borel one)))
  have decay : MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => exp (neg (mul p.1.2 p.2))) :=
    MeasurableMap.comp exp_measurable
      (MeasurableMap.comp neg_measurable (measurable_mul rate value))
  have inside : MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => div (mul (rpow p.1.2 p.1.1) (mul (rpow p.2 (sub p.1.1 one))
        (exp (neg (mul p.1.2 p.2))))) (gamma p.1.1)) :=
    measurable_div (measurable_mul scale (measurable_mul power decay))
      (MeasurableMap.comp gamma_measurable shape)
  exact ofReal_measurable.comp (measurable_piecewise
    (measurable_lt (MeasurableMap.constant _ borel zero) value) inside
    (MeasurableMap.constant _ borel zero))

public theorem density_measurable_slice (shape rate : Carrier) :
    ENNRealMeasurable borel (fun x => ENNReal.finite (density shape rate x)) :=
  Kernel.jointly_measurable_slice (source := Space.product borel borel) (target := borel)
    (density := fun p x => ENNReal.finite (density p.1 p.2 x)) density_measurable (shape, rate)

public theorem density_positive {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) {value : Carrier} (positive : lt zero value) :
    lt zero (density shape rate value).toReal := by
  have formula := div_positive (mul_positive (rpow_positive ratePositive shape)
    (mul_positive (rpow_positive positive (sub shape one)) (exp_positive (neg (mul rate value)))))
    (gamma_positive shapePositive)
  rw [density_of_positive shape rate positive, NNReal.toReal_ofReal formula.1]
  exact formula

/-- On the positive half line the density is its normalizing factor times the
unnormalized weight. -/
public theorem density_product (shape rate : Carrier) {value : Carrier}
    (positive : lt zero value) :
    ENNReal.finite (density shape rate value) =
      ENNReal.mul (ENNReal.ofReal (div (rpow rate shape) (gamma shape)))
        (weight shape rate value) := by
  rw [density_of_positive shape rate positive]
  change ENNReal.ofReal _ = _
  unfold weight Exponential.weight
  rw [← ofReal_mul (rpow_nonnegative _ _) (exp_positive _).1,
    ← ofReal_mul (div_nonnegative (rpow_nonnegative _ _) (gamma_nonnegative shape))
      (mul_nonnegative (rpow_nonnegative _ _) (exp_positive _).1),
    div_eq_mul_inverse, div_eq_mul_inverse]
  congr 1
  ac_rfl

/-- Positive scaling moves the rate into the normalizer. The factor
`rate^shape` times the weight's integral is Euler's integral, finite or not. -/
public theorem weight_integral (shape : Carrier) {rate : Carrier} (positive : lt zero rate) :
    ENNReal.mul (ENNReal.ofReal (rpow rate shape))
        (lintegral (volume.restrict (Ioi zero)) (weight shape rate)) =
      gammaIntegral shape := by
  have scaled := lintegral_volume_restrict_scale rate positive (weight_measurable shape one)
  have pointwise : (volume.restrict (Ioi zero)).AE (fun value =>
      weight shape one (mul rate value) =
        ENNReal.mul (ENNReal.ofReal (rpow rate (sub shape one))) (weight shape rate value)) :=
    (volume.ae_restrict_mem (measurable_ioi zero)).mono (fun value member => by
      unfold weight Exponential.weight
      rw [mul_rpow positive.1 member.1, ofReal_mul (rpow_nonnegative _ _) (rpow_nonnegative _ _),
        one_mul, ENNReal.mul_assoc])
  rw [lintegral_congr_ae pointwise, lintegral_smul _ _ (weight_measurable shape rate)] at scaled
  have split : rpow rate shape = mul rate (rpow rate (sub shape one)) := by
    calc rpow rate shape = rpow rate (add one (sub shape one)) := by rw [add_sub_cancel]
      _ = mul (rpow rate one) (rpow rate (sub shape one)) := rpow_add positive _ _
      _ = mul rate (rpow rate (sub shape one)) := by rw [rpow_one positive.1]
  rw [split, ofReal_mul positive.1 (rpow_nonnegative _ _), ENNReal.mul_assoc, scaled,
    ← ENNReal.mul_assoc, ofReal_mul_ofReal_inverse positive, ENNReal.one_mul]
  rfl

/-- The Gamma weight on the whole line: the shape power, zero off the positive
half line, times the decaying exponential. -/
@[expose] public def lineWeight (shape rate value : Carrier) : ENNReal :=
  ENNReal.mul (shapePower shape value) (Exponential.weight rate value)

public theorem lineWeight_measurable :
    ENNRealMeasurable (Space.product (Space.product borel borel) borel)
      (fun p => lineWeight p.1.1 p.1.2 p.2) := by
  have shape : MeasurableMap (Space.product (Space.product borel borel) borel)
      (Space.product borel borel) (fun p => (p.1.1, p.2)) :=
    Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable borel borel) (Space.first_measurable _ _))
      (Space.second_measurable _ _)
  have rate : MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => p.1.2) :=
    MeasurableMap.comp (Space.second_measurable borel borel) (Space.first_measurable _ _)
  exact (shapePower_jointly_measurable.comp shape).mul
    (ofReal_measurable.comp (MeasurableMap.comp exp_measurable
      (MeasurableMap.comp neg_measurable (measurable_mul rate (Space.second_measurable _ _)))))

/-- The line weight is the Gamma weight restricted to the positive half line. -/
public theorem lineWeight_eq_indicator (shape rate : Carrier) :
    lineWeight shape rate = ennrealIndicator (Ioi zero) (weight shape rate) := by
  funext value
  unfold ennrealIndicator ennrealPiecewise
  by_cases positive : lt zero value
  · rw [ite_eq_left (show Ioi zero value from positive)]
    unfold lineWeight weight
    rw [shapePower_of_positive shape positive]
  · rw [ite_eq_right (show ¬Ioi zero value from positive)]
    unfold lineWeight
    rw [shapePower_of_nonpositive shape (not_lt_iff_le.mp positive), ENNReal.zero_mul]

/-- The Gamma family: the line weight against volume. Its constant fallback one
is arbitrary, because the family has no single degenerate limit. -/
@[expose] public def family : Kernel.NormalizedFamily (Space.product borel borel) borel where
  reference := volume
  referenceFinite := volumeSFinite
  weight parameters value := lineWeight parameters.1 parameters.2 value
  weight_measurable := lineWeight_measurable
  fallback _ := one
  fallback_measurable := MeasurableMap.constant _ borel one

/-- The family's normalizer is the weight's integral over the positive half
line. -/
public theorem family_normalizer (shape rate : Carrier) :
    family.normalizer (shape, rate) =
      lintegral (volume.restrict (Ioi zero)) (weight shape rate) := by
  show lintegral volume (lineWeight shape rate) = _
  rw [lineWeight_eq_indicator, lintegral_indicator _ _ (measurable_ioi zero)]

private theorem scale_cancel {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) :
    ENNReal.mul (ENNReal.ofReal (div (rpow rate shape) (gamma shape)))
      (family.normalizer (shape, rate)) = ENNReal.one := by
  rw [family_normalizer, div_eq_mul_inverse, mul_comm,
    ofReal_mul (inverse_nonnegative (gamma_nonnegative shape)) (rpow_nonnegative _ _),
    ENNReal.mul_assoc, weight_integral shape ratePositive, ← ofReal_gamma shapePositive,
    ENNReal.mul_comm, ofReal_mul_ofReal_inverse (gamma_positive shapePositive)]

/-- A jointly measurable Gamma kernel over all shape/rate pairs. Every fiber is
a probability measure, the Gamma law at positive parameters. -/
@[expose] public def kernel : Kernel (Space.product borel borel) borel :=
  family.kernel

/-- The Gamma law. -/
@[expose] public def law (shape rate : Carrier) : Measure borel :=
  family.law (shape, rate)

public theorem kernel_apply (shape rate : Carrier) : kernel (shape, rate) = law shape rate :=
  rfl

/-- Every Gamma law is a probability measure. -/
public theorem law_isProbability (shape rate : Carrier) :
    Measure.IsProbability (law shape rate) :=
  family.law_isProbability (shape, rate)

/-- At positive shape and rate the law is volume weighted by the density. -/
public theorem law_eq_withDensity {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) :
    law shape rate = volume.withDensity (fun x => ENNReal.finite (density shape rate x)) := by
  apply family.law_eq_of_scale (scale_cancel shapePositive ratePositive)
  intro value
  show ENNReal.finite (density shape rate value) = ENNReal.mul _ (lineWeight shape rate value)
  rw [lineWeight_eq_indicator]
  unfold ennrealIndicator ennrealPiecewise
  by_cases positive : lt zero value
  · rw [ite_eq_left (show Ioi zero value from positive), density_product shape rate positive]
  · rw [ite_eq_right (show ¬Ioi zero value from positive),
      density_of_nonpositive shape rate (not_lt_iff_le.mp positive)]
    exact (ENNReal.mul_zero _).symm

public theorem law_apply {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) {region : Set Carrier} (measurable : borel.Measurable region) :
    law shape rate region = lintegral (volume.restrict region)
      (fun x => ENNReal.finite (density shape rate x)) := by
  rw [law_eq_withDensity shapePositive ratePositive]
  exact volume.withDensity_apply _ measurable

/-- Positive shape and rate give the density unit integral. -/
public theorem density_integral {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) :
    lintegral volume (fun x => ENNReal.finite (density shape rate x)) = ENNReal.one := by
  have total := (law_isProbability shape rate).univ_eq_one
  rwa [law_apply shapePositive ratePositive borel.univ, volume.restrict_univ] at total

/-- Integration against the law agrees with weighting by the explicit density. -/
public theorem law_integral {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral (law shape rate) integrand = lintegral volume
      (fun x => ENNReal.mul (ENNReal.finite (density shape rate x)) (integrand x)) := by
  rw [law_eq_withDensity shapePositive ratePositive]
  exact lintegral_withDensity volume (density_measurable_slice shape rate) measurable

/-- At rate zero the weight's integral is infinite at every positive shape, so no
normalizer exists. -/
public theorem weight_integral_zero_rate {shape : Carrier} (positive : lt zero shape) :
    lintegral (volume.restrict (Ioi zero)) (weight shape zero) = ENNReal.top := by
  rcases ENNReal.eq_top_or_exists_finite
      (lintegral (volume.restrict (Ioi zero)) (weight shape zero)) with infinite | ⟨mass, massEq⟩
  · exact infinite
  · exfalso
    have strict : lt mass.val (add mass.val one) := by
      have raised := add_lt_add_left mass.val one_positive
      rwa [add_zero] at raised
    have targetPositive : lt zero (mul shape (add mass.val one)) :=
      mul_positive positive (lt_of_le_of_lt mass.property strict)
    have boundPositive : lt zero (rpow (mul shape (add mass.val one)) (inverse shape)) :=
      rpow_positive targetPositive _
    have boundPower : rpow (rpow (mul shape (add mass.val one)) (inverse shape)) shape =
        mul shape (add mass.val one) := by
      rw [← rpow_mul targetPositive.1, inverse_mul_cancel (nonzero_of_positive positive),
        rpow_one targetPositive.1]
    have unweighted : weight shape zero =
        (fun value => ENNReal.ofReal (rpow value (sub shape one))) := by
      funext value
      unfold weight Exponential.weight
      rw [zero_mul, neg_zero, exp_zero, ENNReal.ofReal_one, ENNReal.mul_one]
    have included : ENNReal.le
        (lintegral (volume.restrict
            (Ioc zero (rpow (mul shape (add mass.val one)) (inverse shape))))
          (fun value => ENNReal.ofReal (rpow value (sub shape one))))
        (lintegral (volume.restrict (Ioi zero)) (weight shape zero)) := by
      rw [unweighted]
      apply lintegral_mono_measure
      intro set setMeasurable
      rw [Measure.restrict_apply _ _ setMeasurable, Measure.restrict_apply _ _ setMeasurable]
      exact volume.mono (fun _ member => ⟨member.1, member.2.1⟩)
    have quotient : div (mul shape (add mass.val one)) shape = add mass.val one := by
      rw [mul_comm, div_eq_mul_inverse, mul_assoc,
        mul_inverse_cancel (nonzero_of_positive positive),
        mul_one]
    rw [rpow_interval_integral shape _ positive boundPositive, boundPower, quotient, massEq,
      ENNReal.ofReal_le_iff_le_toReal (show ENNReal.Finite (ENNReal.finite mass) from True.intro),
      ENNReal.toReal_finite] at included
    exact strict.2 included

/-- At rate zero the totalized density is zero at every shape. -/
public theorem density_zero_rate (shape value : Carrier) :
    density shape zero value = NNReal.zero := by
  classical
  by_cases positive : lt zero value
  · rw [density_of_positive shape zero positive]
    by_cases vanishing : shape = zero
    · rw [vanishing, gamma_zero, div_zero, NNReal.ofReal_zero]
    · rw [zero_rpow vanishing, zero_mul, zero_div, NNReal.ofReal_zero]
  · exact density_of_nonpositive shape zero (not_lt_iff_le.mp positive)

/-- At shape zero the totalized density is zero at every rate, because the real
projection of the divergent `Γ(0)` is zero. -/
public theorem density_zero_shape (rate value : Carrier) :
    density zero rate value = NNReal.zero := by
  classical
  by_cases positive : lt zero value
  · rw [density_of_positive zero rate positive, gamma_zero, div_zero, NNReal.ofReal_zero]
  · exact density_of_nonpositive zero rate (not_lt_iff_le.mp positive)

/-- Normalization fails at rate zero: at positive shape the law is the fallback
point mass. -/
public theorem law_zero_rate {shape : Carrier} (positive : lt zero shape) :
    law shape zero = Measure.dirac borel one := by
  apply family.law_eq_dirac_of_top
  rw [family_normalizer]
  exact weight_integral_zero_rate positive

/-- Normalization fails at shape zero: at positive rate the law is the fallback
point mass. -/
public theorem law_zero_shape {rate : Carrier} (positive : lt zero rate) :
    law zero rate = Measure.dirac borel one := by
  apply family.law_eq_dirac_of_top
  have scaled := weight_integral zero positive
  rw [rpow_zero, ENNReal.ofReal_one, ENNReal.one_mul, gammaIntegral_zero_eq_top] at scaled
  rw [family_normalizer]
  exact scaled

end
end Problib.Analysis.Gamma
