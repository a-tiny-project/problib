module

public import Problib.Measure.Decomposition.RadonNikodym.Basic
public import Problib.Measure.Decomposition.Hahn
public import Problib.Measure.Additive.Subtract
public import Problib.Measure.Integral.Density.Domination
public import Problib.Measure.Extended.Algebra

set_option autoImplicit false

/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

Adapted from Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Candidate total mass maximization and positive residual contradiction guide the
finite proof architecture. Local mathlib-free measures, integration, and Hahn
comparison supply the underlying steps.
-/

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Finite target and reference measures admit a Radon-Nikodym derivative under
ordinary absolute continuity of the target with respect to the reference.

The proof selects a subdensity that maximizes total weighted mass. An additive
residual contradiction shows the weighted measure equals the target. Unsigned
Hahn comparison supplies the positive dominated increment. -/
public theorem exists_radonNikodymDerivative_of_finite {target reference : Measure space}
    (targetFinite : IsFinite target) (referenceFinite : IsFinite reference)
    (continuous : AbsolutelyContinuous target reference) :
    Nonempty (RadonNikodymDerivative target reference) := by
  classical
  rcases IsSubdensity.exists_maximizer target reference with ⟨density, bound, maximal⟩
  have densityFinite := bound.to_finite targetFinite
  let remainder := Measure.subtract densityFinite bound.bound
  have remainderFinite : IsFinite remainder := targetFinite.subtract densityFinite bound.bound
  have remainderContinuous : AbsolutelyContinuous remainder reference :=
    continuous.of_le (fun set _ => Measure.subtract_le densityFinite bound.bound set)
  have reconstruct : target = reference.withDensity density := by
    apply Classical.byContradiction
    intro different
    have positive : ENNReal.lt ENNReal.zero (remainder Set.univ) := by
      apply ENNReal.zero_lt_iff_ne_zero.mpr
      intro zero
      exact different ((Measure.subtract_eq_zero_iff densityFinite bound.bound).mp
        ((Measure.eq_zero_iff_univ_eq_zero remainder).mpr zero))
    rcases exists_positive_dominated_region remainderFinite referenceFinite
      remainderContinuous positive with
      ⟨factor, _, factorPositive, region, regionMeasurable, regionPositive, dominated⟩
    let increment := ennrealIndicator region (fun _ : alpha => factor)
    have incrementMeasurable : ENNRealMeasurable space increment :=
      ENNRealMeasurable.indicator regionMeasurable (ENNRealMeasurable.constant space factor)
    have incrementBound : ∀ set, space.Measurable set →
        ENNReal.le ((reference.withDensity increment) set) (remainder set) := by
      intro set measurable
      change ENNReal.le
        ((reference.withDensity (ennrealIndicator region (fun _ => factor))) set) (remainder set)
      rw [reference.withDensity_indicator _ regionMeasurable,
        (reference.restrict region).withDensity_const factor,
        Measure.smul_apply_measurable _ _ measurable,
        reference.restrict_apply region measurable]
      exact ENNReal.le_trans
        (dominated (space.inter measurable regionMeasurable) (fun {_} member => member.2))
        (remainder.mono (fun {_} member => member.1))
    have improved : IsSubdensity target reference
        (fun value => ENNReal.add (density value) (increment value)) := by
      refine ⟨ENNRealMeasurable.add bound.measurable incrementMeasurable, ?_⟩
      intro set measurable
      rw [reference.withDensity_add bound.measurable incrementMeasurable, Measure.add_comm]
      exact (Measure.le_subtract_iff densityFinite bound.bound).mp incrementBound set measurable
    have upper := maximal _ improved
    rw [reference.withDensity_add bound.measurable incrementMeasurable,
      Measure.add_apply_measurable _ _ space.univ] at upper
    have nonzero : (reference.withDensity increment) Set.univ ≠ ENNReal.zero := by
      change (reference.withDensity (ennrealIndicator region (fun _ => factor))) Set.univ ≠
        ENNReal.zero
      rw [reference.withDensity_indicator _ regionMeasurable,
        (reference.restrict region).withDensity_const factor,
        Measure.smul_apply_measurable _ _ space.univ, reference.restrict_apply_univ]
      intro zero
      rcases ENNReal.mul_eq_zero_iff.mp zero with factorZero | regionZero
      · exact ENNReal.zero_lt_iff_ne_zero.mp factorPositive factorZero
      · exact ENNReal.zero_lt_iff_ne_zero.mp regionPositive regionZero
    apply nonzero
    apply ENNReal.add_left_cancel_of_finite
      (factor := (reference.withDensity density) Set.univ) densityFinite.univ_finite
    rw [ENNReal.add_zero]
    apply ENNReal.le_antisymm upper
    have lower := ENNReal.add_le_add_left
      (ENNReal.zero_le ((reference.withDensity increment) Set.univ))
      ((reference.withDensity density) Set.univ)
    rw [ENNReal.add_zero] at lower
    exact lower
  exact ⟨{ density := density, density_measurable := bound.measurable, reconstruct := reconstruct }⟩

/-- Classical choice selects a Radon-Nikodym derivative certificate for finite
target and reference measures.

The constructor requires ordinary absolute continuity of the target with
respect to the reference. -/
public noncomputable def RadonNikodymDerivative.ofFinite {target reference : Measure space}
    (targetFinite : IsFinite target) (referenceFinite : IsFinite reference)
    (continuous : AbsolutelyContinuous target reference) :
    RadonNikodymDerivative target reference :=
  Classical.choice (exists_radonNikodymDerivative_of_finite targetFinite referenceFinite continuous)

end Problib.Measure.Measure
