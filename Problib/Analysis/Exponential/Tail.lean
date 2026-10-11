module

public import Problib.Analysis.Exponential.Integral

set_option autoImplicit false

namespace Problib.Analysis.Exponential

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- A decaying exponential with a separately stated positive-rate domain. -/
@[expose] public def weight (rate value : Carrier) : ENNReal :=
  ENNReal.ofReal (exp (neg (mul rate value)))

public theorem weight_measurable (rate : Carrier) : ENNRealMeasurable borel (weight rate) :=
  ofReal_measurable.comp (MeasurableMap.comp exp_measurable (MeasurableMap.comp neg_measurable
    (measurable_mul (MeasurableMap.constant borel borel rate) (MeasurableMap.identity borel))))

public theorem weight_add (rate shift value : Carrier) :
    weight rate (add shift value) = ENNReal.mul (weight rate shift) (weight rate value) := by
  unfold weight
  have negative : neg (add (mul rate shift) (mul rate value)) =
      add (neg (mul rate shift)) (neg (mul rate value)) := additive.group.neg_add_distrib _ _
  rw [mul_add, negative, exp_add, ofReal_mul (exp_positive _).1 (exp_positive _).1]

/-- Positive scaling of the proved unit exponential integral. -/
public theorem integral (rate : Carrier) (positive : lt zero rate) :
    lintegral (volume.restrict (Ioi zero)) (weight rate) = ENNReal.ofReal (inverse rate) := by
  have scaled := lintegral_volume_restrict_scale rate positive
    (ofReal_measurable.comp (MeasurableMap.comp exp_measurable neg_measurable))
  rw [unit_integral, ENNReal.mul_one] at scaled
  exact scaled

private theorem translate_positive_ray (threshold : Carrier) :
    (volume.restrict (Ioi zero)).map (add threshold) (translate_measurable threshold) =
      volume.restrict (Ioi threshold) := by
  have mapped := Measure.map_restrict volume (add threshold) (translate_measurable threshold) (measurable_ioi threshold)
  have preimage : Set.preimage (add threshold) (Ioi threshold) = Ioi zero := by
    apply Set.ext
    intro value
    have same := @add_lt_add_left_iff zero value threshold
    rw [add_zero] at same
    exact same
  rw [preimage, map_volume_translate] at mapped
  exact mapped

/-- The exponential tail integral at any real threshold, including negative thresholds. -/
public theorem tail (rate threshold : Carrier) (positive : lt zero rate) :
    lintegral (volume.restrict (Ioi threshold)) (weight rate) =
      ENNReal.mul (weight rate threshold) (ENNReal.ofReal (inverse rate)) := by
  rw [← translate_positive_ray threshold,
    lintegral_map _ _ (translate_measurable threshold) (weight_measurable rate)]
  have same : (fun value => weight rate (add threshold value)) =
      (fun value => ENNReal.mul (weight rate threshold) (weight rate value)) := funext (weight_add rate threshold)
  rw [same, lintegral_smul _ _ (weight_measurable rate), integral rate positive]

/-- Closing the finite endpoint leaves the tail integral unchanged. -/
public theorem tail_closed (rate threshold : Carrier) (positive : lt zero rate) :
    lintegral (volume.restrict (Ici threshold)) (weight rate) =
      ENNReal.mul (weight rate threshold) (ENNReal.ofReal (inverse rate)) := by
  rw [← restrict_volume_ioi, tail rate threshold positive]

end
end Problib.Analysis.Exponential
