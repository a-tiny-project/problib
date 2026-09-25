module

public import Problib.Analysis.SquareIntegral
public import Problib.Analysis.Exponential.Tail

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The unnormalized centered Gaussian weight with a positive coefficient domain. -/
@[expose] public def bell (coefficient value : Carrier) : ENNReal :=
  Exponential.weight coefficient (mul value value)

public theorem bell_measurable (coefficient : Carrier) : ENNRealMeasurable borel (bell coefficient) :=
  (Exponential.weight_measurable coefficient).comp
    (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel))

public theorem bell_even (coefficient value : Carrier) : bell coefficient (neg value) = bell coefficient value :=
  congrArg (Exponential.weight coefficient) (multiplicativeSelection.ring.neg_mul_neg value value)

private theorem inverse_product (coefficient : Carrier) (positive : lt zero coefficient) :
    mul (inverse (selection.ofRat 2)) (inverse coefficient) = inverse (mul (selection.ofRat 2) coefficient) := by
  have first := (positive_iff_nonnegative_and_nonzero.mp ofRat_two_positive).2
  have second := (positive_iff_nonnegative_and_nonzero.mp positive).2
  have both := (positive_iff_nonnegative_and_nonzero.mp (mul_positive ofRat_two_positive positive)).2
  apply mul_right_cancel_of_nonzero both
  rw [inverse_mul_cancel both, mul_assoc,
    ← mul_assoc (inverse coefficient), mul_comm (inverse coefficient) (selection.ofRat 2),
    mul_assoc (selection.ofRat 2), inverse_mul_cancel second, mul_one, inverse_mul_cancel first]

/-- The coordinate-weighted Gaussian tail is evaluated without differentiating an integral. -/
public theorem weighted_tail (coefficient threshold : Carrier) (positive : lt zero coefficient)
    (thresholdPositive : lt zero threshold) :
    lintegral (volume.restrict (Ici threshold))
      (fun value => ENNReal.mul (ENNReal.ofReal value) (bell coefficient value)) =
        ENNReal.mul (ENNReal.ofReal (inverse (mul (selection.ofRat 2) coefficient))) (bell coefficient threshold) := by
  have squaredPositive := mul_positive thresholdPositive thresholdPositive
  have sourceIntersection : Set.inter (Ici threshold) (Ioi zero) = Ici threshold :=
    Set.ext (fun _ => ⟨fun member => member.1, fun member => ⟨member, lt_of_lt_of_le thresholdPositive member⟩⟩)
  have targetIntersection : Set.inter (Ici (mul threshold threshold)) (Ioi zero) = Ici (mul threshold threshold) :=
    Set.ext (fun _ => ⟨fun member => member.1, fun member => ⟨member, lt_of_lt_of_le squaredPositive member⟩⟩)
  have same := (volume.ae_restrict_mem (measurable_ioi zero)).mono (fun value member => show
      ENNReal.mul (ENNReal.ofReal value)
        (ennrealIndicator (Ici (mul threshold threshold)) (Exponential.weight coefficient) (mul value value)) =
      ennrealIndicator (Ici threshold) (fun value => ENNReal.mul (ENNReal.ofReal value) (bell coefficient value)) value from by
    have ordered : Ici (mul threshold threshold) (mul value value) ↔ Ici threshold value :=
      square_le_iff ⟨threshold, thresholdPositive.1⟩ ⟨value, member.1⟩
    classical
    by_cases inside : Ici threshold value
    · simp only [ennrealIndicator, ennrealPiecewise, ordered, if_pos inside, bell]
    · simp only [ennrealIndicator, ennrealPiecewise, ordered, if_neg inside, ENNReal.mul_zero])
  have substitution := SquareIntegral.integral
    (ENNRealMeasurable.indicator (measurable_ici (mul threshold threshold)) (Exponential.weight_measurable coefficient))
  rw [lintegral_congr_ae same, lintegral_indicator _ _ (measurable_ici threshold),
    Measure.restrict_restrict volume _ (measurable_ici threshold), sourceIntersection,
    lintegral_indicator _ _ (measurable_ici (mul threshold threshold)),
    Measure.restrict_restrict volume _ (measurable_ici (mul threshold threshold)), targetIntersection,
    Exponential.tail_closed coefficient _ positive] at substitution
  have constants : ENNReal.mul (ENNReal.ofReal (inverse (selection.ofRat 2)))
      (ENNReal.ofReal (inverse coefficient)) = ENNReal.ofReal (inverse (mul (selection.ofRat 2) coefficient)) := by
    rw [← ofReal_mul (inverse_of_positive_positive ofRat_two_positive).1 (inverse_of_positive_positive positive).1,
      inverse_product coefficient positive]
  exact substitution.trans (by rw [ENNReal.mul_comm (Exponential.weight _ _), ← ENNReal.mul_assoc, constants]; rfl)

/-- Layer cake turns the positive second moment into the already evaluated weighted tail. -/
public theorem positive_second_weighted_integral (coefficient : Carrier) (positive : lt zero coefficient) :
    lintegral (volume.restrict (Ioi zero)) (fun value =>
      ENNReal.mul (ENNReal.ofReal (mul value value)) (bell coefficient value)) =
        ENNReal.mul (ENNReal.ofReal (inverse (mul (selection.ofRat 2) coefficient)))
          (lintegral (volume.restrict (Ioi zero)) (bell coefficient)) := by
  let weight := fun value => ENNReal.mul (ENNReal.ofReal value) (bell coefficient value)
  have weightMeasurable : ENNRealMeasurable borel weight := ofReal_measurable.mul (bell_measurable coefficient)
  have same := (volume.ae_restrict_mem (measurable_ioi zero)).mono (fun value member => show
      ENNReal.mul (ENNReal.ofReal (mul value value)) (bell coefficient value) =
        ENNReal.mul (weight value) (ENNReal.ofReal value) from by
    rw [ofReal_mul member.1 member.1, ENNReal.mul_assoc, ENNReal.mul_comm (ENNReal.ofReal value) (bell coefficient value)]
    exact (ENNReal.mul_assoc _ _ _).symm)
  rw [lintegral_congr_ae same,
    lintegral_layer_cake _ (volumeSFinite.restrict (measurable_ioi zero)) (MeasurableMap.identity borel) weightMeasurable]
  have fibers (level : Carrier) :
      lintegral (volume.restrict (Ioi zero)) (ennrealIndicator (fun value => Ioc zero value level) weight) =
        ennrealIndicator (Ioi zero)
          (fun level => ENNReal.mul (ENNReal.ofReal (inverse (mul (selection.ofRat 2) coefficient))) (bell coefficient level)) level := by
    classical
    by_cases levelPositive : lt zero level
    · have same : (fun value => Ioc zero value level) = Ici level :=
        Set.ext (fun _ => ⟨fun member => member.2, fun member => ⟨levelPositive, member⟩⟩)
      have intersection : Set.inter (Ici level) (Ioi zero) = Ici level :=
        Set.ext (fun _ => ⟨fun member => member.1, fun member => ⟨member, lt_of_lt_of_le levelPositive member⟩⟩)
      rw [same, lintegral_indicator _ _ (measurable_ici level),
        Measure.restrict_restrict volume _ (measurable_ici level), intersection]
      simpa only [ennrealIndicator, ennrealPiecewise, Ioi, if_pos levelPositive] using weighted_tail coefficient level positive levelPositive
    · have empty : ennrealIndicator (fun value => Ioc zero value level) weight = (fun _ => ENNReal.zero) := by
        funext value
        simp only [ennrealIndicator, ennrealPiecewise, if_neg (fun member : Ioc zero value level => levelPositive member.1)]
      rw [empty, lintegral_zero]
      simp only [ennrealIndicator, ennrealPiecewise, Ioi, if_neg levelPositive]
  rw [lintegral_congr volume fibers, lintegral_indicator volume _ (measurable_ioi zero),
    lintegral_smul _ _ (bell_measurable coefficient)]

/-- Reflection extends the positive second-moment formula to the whole line, even before proving finiteness. -/
public theorem second_weighted_integral (coefficient : Carrier) (positive : lt zero coefficient) :
    lintegral volume (fun value => ENNReal.mul (ENNReal.ofReal (mul value value)) (bell coefficient value)) =
      ENNReal.mul (ENNReal.ofReal (inverse (mul (selection.ofRat 2) coefficient))) (lintegral volume (bell coefficient)) := by
  have squareMeasurable : ENNRealMeasurable borel (fun value => ENNReal.ofReal (mul value value)) :=
    ofReal_measurable.comp (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel))
  have even : ∀ value, ENNReal.mul (ENNReal.ofReal (mul (neg value) (neg value))) (bell coefficient (neg value)) =
      ENNReal.mul (ENNReal.ofReal (mul value value)) (bell coefficient value) := by
    intro value
    have squared : mul (neg value) (neg value) = mul value value := multiplicativeSelection.ring.neg_mul_neg _ _
    rw [squared, bell_even]
  rw [lintegral_volume_even (squareMeasurable.mul (bell_measurable coefficient)) even,
    positive_second_weighted_integral coefficient positive,
    lintegral_volume_even (bell_measurable coefficient) (bell_even coefficient),
    ← ENNReal.mul_assoc, ENNReal.mul_comm (ENNReal.add ENNReal.one ENNReal.one), ENNReal.mul_assoc]

end
end Problib.Analysis.Gaussian
