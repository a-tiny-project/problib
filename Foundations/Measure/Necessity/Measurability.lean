module

public import Foundations.Measure.Integral.Lebesgue.Zero
public import Foundations.Measure.Integral.Simple.Integral.Transport
public import Foundations.Measure.Additive.Finite

set_option autoImplicit false

namespace Foundations.Measure.Necessity.Measurability

open Foundations.Real

/-- Dirac measure on the indiscrete two-point space focused at true. -/
public noncomputable def reference : Measure (Space.indiscrete Bool) :=
  Measure.dirac (Space.indiscrete Bool) true

/-- The indiscrete Dirac measure is a probability measure. -/
public theorem reference_probability : Measure.IsProbability reference :=
  Measure.IsProbability.dirac _ _

/-- Indicator function taking value zero at false and value one at true. -/
@[expose] public noncomputable def function : Bool → ENNReal
  | false => ENNReal.zero
  | true => ENNReal.one

private theorem simple_values_equal (simple : SimpleFunction (Space.indiscrete Bool)) :
    simple true = simple false := by
  rcases (Space.indiscrete_measurable_iff _).mp
    (simple.fiber_measurable (simple false)) with empty | whole
  · have member : simple.fiber (simple false) false := rfl
    rw [empty] at member
    exact False.elim member
  · change simple.fiber (simple false) true
    rw [whole]
    exact True.intro

/-- Lower Lebesgue integral of the nonmeasurable indicator is zero because any
minorizing simple function must take identical values at both points. -/
public theorem lower_integral_zero : lintegral reference function = ENNReal.zero := by
  apply ENNReal.eqZeroOfLeZero
  apply lintegral_le
  intro lower included
  rw [reference, lower.integral_dirac, simple_values_equal lower]
  exact included false

/-- The indicator function does not vanish almost everywhere because its support
point has unit Dirac mass. -/
public theorem function_not_ae_zero :
    ¬reference.AEEq function (fun _ => ENNReal.zero) := by
  intro equal
  rcases (show reference.NullSet
      (Set.complement (fun value => function value = ENNReal.zero)) from equal
    ).exists_measurable_superset with ⟨superset, measurable, included, nullSet⟩
  have member : superset true := included ENNReal.oneNeZero
  change reference superset = ENNReal.zero at nullSet
  rw [reference, Measure.dirac_apply_of_mem _ _ measurable member] at nullSet
  exact ENNReal.oneNeZero nullSet

/-- The indicator function is not measurable on the indiscrete space. -/
public theorem function_not_measurable :
    ¬ENNRealMeasurable (Space.indiscrete Bool) function := by
  intro measurable
  exact function_not_ae_zero (ae_zero_of_lintegral_eq_zero measurable lower_integral_zero)

/-- Vanishing lower integral does not imply almost-everywhere vanishing without
integrand measurability, even on a probability space. -/
public theorem probability_zero_lower_integral_does_not_imply_ae_zero :
    ¬(∀ {alpha : Type} {space : Space alpha} (measure : Measure space),
      Measure.IsProbability measure → ∀ (function : alpha → ENNReal),
      lintegral measure function = ENNReal.zero →
      measure.AEEq function (fun _ => ENNReal.zero)) := by
  intro converse
  exact function_not_ae_zero
    (converse reference reference_probability function lower_integral_zero)

end Foundations.Measure.Necessity.Measurability
