module

public import Foundations.Measure.Integral.Lebesgue.AlmostEverywhere
public import Foundations.Measure.Uniform

set_option autoImplicit false

namespace Foundations.Measure.Necessity.AlmostEverywhere

open Foundations.Real
open Foundations.Real.Construction

public noncomputable def zeroSpike : SimpleFunction Real.borel :=
  SimpleFunction.indicator (Set.singleton Dedekind.zero)
    (Real.measurable_singleton Dedekind.zero) ENNReal.one

public theorem zeroSpike_measurable :
    ENNRealMeasurable Real.borel zeroSpike :=
  zeroSpike.measurable

public theorem zeroSpike_at_zero : zeroSpike Dedekind.zero = ENNReal.one :=
  SimpleFunction.indicator_apply_of_mem _ _ _ _ rfl

public theorem zeroSpike_ae_zero :
    Real.restrictedUnit.AEEq zeroSpike (fun _ => ENNReal.zero) := by
  classical
  have nullSingleton : Real.restrictedUnit.NullSet
      (Set.singleton Dedekind.zero) :=
    Measure.NullSet.restrict (Real.volume_singleton Dedekind.zero) Real.unitSet
  apply nullSingleton.mono
  intro value failure
  apply Classical.byContradiction
  intro outside
  exact failure (SimpleFunction.indicator_apply_of_not_mem _ _ _ _ outside)

public theorem zeroSpike_lintegral :
    lintegral Real.restrictedUnit zeroSpike = ENNReal.zero :=
  lintegral_eq_zero_of_ae_zero zeroSpike_ae_zero

/-- A measurable singleton spike under restricted-unit Lebesgue probability is
almost-everywhere zero and has zero lower integral, yet takes value one at zero.
The counterexample separates almost-everywhere vanishing from pointwise
vanishing in continuous probability. The witness does not define topological
support or discharge `PPL.Trace.SupportBridge`. -/
public theorem ae_equality_does_not_imply_pointwise_equality :
    Measure.IsProbability Real.restrictedUnit ∧
      ENNRealMeasurable Real.borel zeroSpike ∧
      Real.restrictedUnit.AEEq zeroSpike (fun _ => ENNReal.zero) ∧
      lintegral Real.restrictedUnit zeroSpike = ENNReal.zero ∧
      zeroSpike Dedekind.zero ≠ ENNReal.zero := by
  refine ⟨Real.restrictedUnit_isProbability, zeroSpike_measurable,
    zeroSpike_ae_zero, zeroSpike_lintegral, ?_⟩
  rw [zeroSpike_at_zero]
  exact ENNReal.oneNeZero

end Foundations.Measure.Necessity.AlmostEverywhere
