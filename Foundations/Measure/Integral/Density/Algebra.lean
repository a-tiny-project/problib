module

public import Foundations.Measure.Integral.Density.Basic
public import Foundations.Measure.Integral.Density.Restrict
public import Foundations.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Weighting a measure by a constant density equals scalar multiplication by
that factor. -/
public theorem withDensity_const (measure : Measure space) (factor : ENNReal) :
    measure.withDensity (fun _ => factor) = Measure.smul factor measure := by
  apply Measure.ext
  intro set measurable
  rw [measure.withDensity_apply (fun _ => factor) measurable,
    lintegral_const, measure.restrict_apply_univ,
    Measure.smul_apply_measurable factor measure measurable]

/-- Weighting a measure by the zero density produces the zero measure. -/
public theorem withDensity_zero (measure : Measure space) :
    measure.withDensity (fun _ => ENNReal.zero) = Measure.zero space := by
  rw [measure.withDensity_const, Measure.zero_smul]

/-- Weighting a measure by the constant unit density reproduces the original
measure. -/
public theorem withDensity_one (measure : Measure space) :
    measure.withDensity (fun _ => ENNReal.one) = measure := by
  rw [measure.withDensity_const, Measure.one_smul]

/-- Density weighting distributes over addition of measurable densities. -/
public theorem withDensity_add (measure : Measure space) {left right : alpha → ENNReal}
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right) :
    measure.withDensity (fun value => ENNReal.add (left value) (right value)) =
      Measure.add (measure.withDensity left) (measure.withDensity right) := by
  apply Measure.ext
  intro set measurable
  rw [Measure.add_apply_measurable _ _ measurable, measure.withDensity_apply _ measurable,
    measure.withDensity_apply _ measurable, measure.withDensity_apply _ measurable]
  exact lintegral_add _ leftMeasurable rightMeasurable

/-- Weighting by the indicator of a density on a measurable region equals
weighting the restricted measure by the original density. Density measurability
is not required. -/
public theorem withDensity_indicator (measure : Measure space) (density : alpha → ENNReal)
    {region : Set alpha} (regionMeasurable : space.Measurable region) :
    measure.withDensity (ennrealIndicator region density) =
      (measure.restrict region).withDensity density := by
  apply Measure.ext
  intro set measurable
  rw [measure.withDensity_apply _ measurable,
    (measure.restrict region).withDensity_apply _ measurable,
    lintegral_indicator _ region regionMeasurable density,
    measure.restrict_restrict set regionMeasurable,
    measure.restrict_restrict region measurable, Set.inter_comm region set]

/-- Weighting by a piecewise density on a measurable region equals the sum of
the two respective weighted restrictions. -/
public theorem withDensity_piecewise (measure : Measure space)
    {inside outside : alpha → ENNReal} {region : Set alpha}
    (regionMeasurable : space.Measurable region)
    (insideMeasurable : ENNRealMeasurable space inside)
    (outsideMeasurable : ENNRealMeasurable space outside) :
    measure.withDensity (ennrealPiecewise region inside outside) =
      Measure.add ((measure.restrict region).withDensity inside)
        ((measure.restrict (Set.complement region)).withDensity outside) := by
  have equal : ennrealPiecewise region inside outside =
      (fun value => ENNReal.add (ennrealIndicator region inside value)
        (ennrealIndicator (Set.complement region) outside value)) := by
    funext value
    classical
    by_cases member : region value
    · simp only [ennrealIndicator, ennrealPiecewise, Set.complement, member,
        if_true, not_true_eq_false, if_false, ENNReal.addZero]
    · simp only [ennrealIndicator, ennrealPiecewise, Set.complement, member,
        if_true, not_false_eq_true, if_false, ENNReal.zeroAdd]
  rw [equal, measure.withDensity_add (ENNRealMeasurable.indicator regionMeasurable insideMeasurable)
    (ENNRealMeasurable.indicator (space.complement regionMeasurable) outsideMeasurable),
    measure.withDensity_indicator inside regionMeasurable,
    measure.withDensity_indicator outside (space.complement regionMeasurable)]

/-- Weighting by the maximum of two measurable densities equals the sum of
the two respective weighted restrictions. -/
public theorem withDensity_max (measure : Measure space) {left right : alpha → ENNReal}
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right) :
    measure.withDensity (fun value => ENNReal.max (left value) (right value)) =
      Measure.add
        ((measure.restrict (fun value => ENNReal.le (left value) (right value))).withDensity right)
        ((measure.restrict (Set.complement
          (fun value => ENNReal.le (left value) (right value)))).withDensity left) := by
  have equal : (fun value => ENNReal.max (left value) (right value)) =
      ennrealPiecewise (fun value => ENNReal.le (left value) (right value)) right left := by
    funext value
    classical
    unfold ENNReal.max ennrealPiecewise
    split <;> rfl
  rw [equal]
  exact measure.withDensity_piecewise (leftMeasurable.le_set rightMeasurable)
    rightMeasurable leftMeasurable

/-- Evaluates the measure weighted by the pointwise supremum of a monotone
sequence of measurable densities on a measurable probe set.

Equates that probe mass to the supremum of the individual weighted masses. -/
public theorem withDensity_iSup_apply (measure : Measure space)
    (densities : Nat → alpha → ENNReal)
    (measurable : ∀ index, ENNRealMeasurable space (densities index))
    (monotone : ∀ stage value, ENNReal.le (densities stage value) (densities (stage + 1) value))
    {set : Set alpha} (setMeasurable : space.Measurable set) :
    (measure.withDensity (fun value => ENNReal.iSup (fun index => densities index value))) set =
      ENNReal.iSup (fun index => (measure.withDensity (densities index)) set) := by
  rw [measure.withDensity_apply _ setMeasurable, lintegral_iSup _ densities measurable monotone]
  apply congrArg ENNReal.iSup
  funext index
  exact (measure.withDensity_apply _ setMeasurable).symm

/-- Weighting by a countable sum of measurable densities equals the countable
sum of the individual weighted measures. -/
public theorem withDensity_tsum (measure : Measure space) (densities : Nat → alpha → ENNReal)
    (measurable : ∀ index, ENNRealMeasurable space (densities index)) :
    measure.withDensity (fun value => ENNReal.tsum (fun index => densities index value)) =
      Measure.sum (fun index => measure.withDensity (densities index)) := by
  apply Measure.ext
  intro set setMeasurable
  rw [measure.withDensity_apply _ setMeasurable,
    Measure.sum_apply _ setMeasurable, lintegral_tsum _ densities measurable]
  apply ENNReal.tsumCongr
  intro index
  exact (measure.withDensity_apply _ setMeasurable).symm

end Foundations.Measure.Measure
