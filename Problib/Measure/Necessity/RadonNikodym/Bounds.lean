module

public import Problib.Measure.Decomposition.RadonNikodym.Basic
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Necessity.Density

/-!
# Necessity witnesses for Radon-Nikodym bounds and domination

This module provides counterexamples for derivative bounds and reference
finiteness.
A self-derivative can take value infinity on a null set.
An s-finite reference can dominate a Dirac probability measure without
admitting a derivative.
-/

set_option autoImplicit false

namespace Problib.Measure.Necessity.RadonNikodym

open Problib.Real

/-- A probability measure self-derivative can take the value infinity at a
reference-null point. -/
public theorem probability_derivative_need_not_be_bounded :
    ∃ reference : Measure (Space.discrete Bool),
      Measure.IsProbability reference ∧
        ∃ derivative : Measure.RadonNikodymDerivative reference reference,
          derivative.density false = ENNReal.top := by
  let reference := Measure.dirac (Space.discrete Bool) true
  let density : Bool → ENNReal := fun value => if value then ENNReal.one else ENNReal.top
  have measurable : ENNRealMeasurable (Space.discrete Bool) density := fun _ => True.intro
  have equal : reference.AEEq density (fun _ => ENNReal.one) := by
    change reference (fun value => ¬density value = ENNReal.one) = ENNReal.zero
    exact Measure.dirac_apply_of_not_mem (Space.discrete Bool) true True.intro
      (by simp [density])
  refine ⟨reference, Measure.IsProbability.dirac _ _, ?_⟩
  refine ⟨{
    density := density
    density_measurable := measurable
    reconstruct := ?_
  }, rfl⟩
  change reference = reference.withDensity density
  rw [Measure.withDensity_congr_ae equal, reference.withDensity_one]

/-- A probability Dirac measure dominated on measurable sets by an s-finite
reference measure can lack a Radon-Nikodym derivative. -/
public theorem s_finite_domination_no_derivative :
    ∃ target reference : Measure (Space.discrete Unit),
      Measure.IsProbability target ∧ Nonempty (Measure.SFinite reference) ∧
        (∀ set, (Space.discrete Unit).Measurable set → ENNReal.le (target set) (reference set)) ∧
          ¬Nonempty (Measure.RadonNikodymDerivative target reference) := by
  refine ⟨Measure.dirac (Space.discrete Unit) (), Density.reference,
    Measure.IsProbability.dirac _ _, ⟨Density.reference_sFinite⟩, ?_, ?_⟩
  · intro set measurable
    rw [Density.reference_eq_top_smul, Measure.smul_apply_measurable _ _ measurable]
    have included := ENNReal.mul_le_mul_right (ENNReal.le_top ENNReal.one)
      ((Measure.dirac (Space.discrete Unit) ()) set)
    rw [ENNReal.one_mul] at included
    exact included
  · rintro ⟨derivative⟩
    exact Density.dirac_has_no_density derivative.density derivative.reconstruct

end Problib.Measure.Necessity.RadonNikodym
