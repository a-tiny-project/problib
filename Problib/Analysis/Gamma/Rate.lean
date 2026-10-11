module

public import Problib.Analysis.Gamma.Density
public import Problib.Measure.Real.Affine
public import Problib.Measure.Additive.Comap
import Problib.Real.Grind

/-! The rate of the Gamma law is a scale.

Dividing a rate-one Gamma draw by a positive rate gives the Gamma law at that
rate (`law_map_div`), and every Gamma law lives on the positive half line
(`law_positive`), so it is a law on the positive reals (`law_comap_map`). At a positive point the density at rate `r` is `r` times
the rate-one density at `r·x`, and scaling volume by `r` divides it by `r`.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Gamma

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- At every point the density at rate `r` is `r` times the rate-one density
at `r·x`. -/
public theorem density_scale {shape rate : Carrier} (ratePositive : lt zero rate) (value : Carrier) :
    ENNReal.finite (density shape rate value) =
      ENNReal.mul (ENNReal.ofReal rate) (ENNReal.finite (density shape one (mul rate value))) := by
  by_cases positive : lt zero value
  · have scaledPositive : lt zero (mul rate value) := mul_positive ratePositive positive
    rw [density_of_positive shape rate positive, density_of_positive shape one scaledPositive]
    change ENNReal.ofReal _ = ENNReal.mul _ (ENNReal.ofReal _)
    have split : rpow rate shape = mul rate (rpow rate (sub shape one)) := by
      calc rpow rate shape = rpow rate (add one (sub shape one)) := by rw [add_sub_cancel]
        _ = mul (rpow rate one) (rpow rate (sub shape one)) := rpow_add ratePositive _ _
        _ = mul rate (rpow rate (sub shape one)) := by rw [rpow_one ratePositive.1]
    have formula := div_nonnegative (mul_nonnegative (rpow_nonnegative one shape)
      (mul_nonnegative (rpow_nonnegative (mul rate value) (sub shape one))
        (exp_positive (neg (mul one (mul rate value)))).1)) (gamma_nonnegative shape)
    rw [← ofReal_mul ratePositive.1 formula, mul_rpow ratePositive.1 positive.1, one_rpow, split,
      one_mul]
    congr 1
    simp only [div_eq_mul_inverse]
    real_grind
  · have nonpositive := not_lt_iff_le.mp positive
    have scaledNonpositive : le (mul rate value) zero := by
      have := mul_le_mul_nonnegative_left nonpositive ratePositive.1
      rwa [mul_zero] at this
    rw [density_of_nonpositive shape rate nonpositive,
      density_of_nonpositive shape one scaledNonpositive]
    exact (ENNReal.mul_zero _).symm

/-- At a positive shape and rate the law puts all its mass on the positive
half line. -/
public theorem law_positive {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) : law shape rate (Ioi zero) = ENNReal.one := by
  rw [law_apply shapePositive ratePositive (measurable_ioi zero),
    ← lintegral_indicator _ _ (measurable_ioi zero)]
  have pointwise : ennrealIndicator (Ioi zero) (fun x => ENNReal.finite (density shape rate x)) =
      fun x => ENNReal.finite (density shape rate x) := by
    classical
    funext value
    by_cases positive : Ioi zero value
    · rw [ennrealIndicator_of_mem positive]
    · rw [ennrealIndicator_of_not_mem positive,
        density_of_nonpositive shape rate (not_lt_iff_le.mp positive)]
      rfl
  rw [pointwise, density_integral shapePositive ratePositive]

/-- At a positive shape and rate the law gives the nonpositive half line no
mass. -/
public theorem law_nonpositive {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) : law shape rate (Iic zero) = ENNReal.zero := by
  rw [law_apply shapePositive ratePositive (measurable_iic zero)]
  have pointwise : (volume.restrict (Iic zero)).AEEq
      (fun value => ENNReal.finite (density shape rate value)) (fun _ => ENNReal.zero) :=
    (volume.ae_restrict_mem (measurable_iic zero)).mono fun value member => by
      show ENNReal.finite (density shape rate value) = ENNReal.zero
      rw [density_of_nonpositive shape rate member]
      rfl
  rw [lintegral_congr_ae pointwise, lintegral_zero]

/-- A Gamma law read on the positive reals and carried back to the line is the
law itself. -/
public theorem law_comap_map {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) :
    ((law shape rate).comap (MeasurableEmbedding.subtype (Ioi zero) (measurable_ioi zero))).map
        (MeasurableEmbedding.subtype (Ioi zero) (measurable_ioi zero)).function
        (MeasurableEmbedding.subtype (Ioi zero) (measurable_ioi zero)).measurable =
      law shape rate := by
  apply Measure.map_comap_of_complement_null
  apply ENNReal.le_antisymm _ (ENNReal.zero_le _)
  rw [← law_nonpositive shapePositive ratePositive]
  exact (law shape rate).mono fun value outside =>
    not_lt_iff_le.mp fun positive => outside ⟨⟨value, positive⟩, rfl⟩

/-- Dividing by a positive rate is measurable. -/
public theorem div_rate_measurable (rate : Carrier) :
    MeasurableMap borel borel (fun value => div value rate) :=
  measurable_div (MeasurableMap.identity borel) (MeasurableMap.constant borel borel rate)

/-- A rate-one Gamma draw divided by a positive rate has the Gamma law at that
rate. -/
public theorem law_map_div {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) :
    (law shape one).map (fun value => div value rate) (div_rate_measurable rate) =
      law shape rate := by
  apply Measure.ext
  intro region measurable
  have preimageMeasurable := div_rate_measurable rate measurable
  rw [Measure.map_apply _ _ _ measurable, law_eq_withDensity shapePositive one_positive,
    law_eq_withDensity shapePositive ratePositive, Measure.withDensity_apply _ _ preimageMeasurable,
    Measure.withDensity_apply _ _ measurable,
    ← lintegral_indicator _ _ preimageMeasurable, ← lintegral_indicator _ _ measurable]
  let rateOne := ennrealIndicator (Set.preimage (fun value => div value rate) region)
    (fun value => ENNReal.finite (density shape one value))
  have rateOneMeasurable : ENNRealMeasurable borel rateOne :=
    ENNRealMeasurable.indicator preimageMeasurable (density_measurable_slice shape one)
  have pointwise : ennrealIndicator region (fun value => ENNReal.finite (density shape rate value)) =
      fun value => ENNReal.mul (ENNReal.ofReal rate) (rateOne (mul rate value)) := by
    classical
    funext value
    have back : div (mul rate value) rate = value := by
      have cancel := mul_inverse_cancel (nonzero_of_positive ratePositive)
      rw [div_eq_mul_inverse]; real_grind
    show _ = ENNReal.mul (ENNReal.ofReal rate) (ennrealIndicator
      (Set.preimage (fun value => div value rate) region)
      (fun value => ENNReal.finite (density shape one value)) (mul rate value))
    by_cases inside : region value
    · have member : Set.preimage (fun value => div value rate) region (mul rate value) := by
        show region (div (mul rate value) rate); rw [back]; exact inside
      rw [ennrealIndicator_of_mem inside, ennrealIndicator_of_mem member, density_scale ratePositive]
    · have nonmember : ¬Set.preimage (fun value => div value rate) region (mul rate value) := by
        show ¬region (div (mul rate value) rate); rw [back]; exact inside
      rw [ennrealIndicator_of_not_mem inside, ennrealIndicator_of_not_mem nonmember,
        ENNReal.mul_zero]
  rw [pointwise, lintegral_smul _ _ (rateOneMeasurable.comp (scale_measurable rate ratePositive.1)),
    lintegral_volume_scale rate ratePositive rateOneMeasurable, ← ENNReal.mul_assoc,
    ofReal_mul_ofReal_inverse ratePositive, ENNReal.one_mul]

end

end Problib.Analysis.Gamma
