module

public import Problib.Measure.Distribution.Bounds

set_option autoImplicit false

namespace Problib.Measure.Necessity.Distribution

open Problib.Real.Construction
open Problib.Measure.Real

/-- Counterexample refuting automatic interpolation of supplied bounds.
A supplied bound at threshold zero is never active for any unit-interval point.
Constructs a distribution function satisfying the vacuous strict-initial bound
whose value at zero is one rather than zero. -/
public theorem zero_threshold_counterexample :
    ∃ distribution : DistributionFunction,
      (∀ point : UnitInterval, Dedekind.lt point.val unitZero.val →
        Dedekind.le (distribution.function point).val unitZero.val) ∧
      distribution.function unitZero ≠ unitZero := by
  let distribution : DistributionFunction := {
    function := fun _ => unitOne
    monotone := fun _ => Dedekind.le_refl _
    upper := rfl
    right_continuous := fun point room upper above => ⟨unitOne, room, above⟩
  }
  refine ⟨distribution, ?_, ?_⟩
  · intro point below
    exact False.elim (below.2 point.property.1)
  · intro equal
    exact Dedekind.one_ne_zero (congrArg Subtype.val equal)

/-- A supplied bound at threshold zero never activates on the unit interval.
Because no unit-interval point is strictly below zero, the bound never
activates and the construction evaluates to one everywhere. -/
public theorem zero_threshold_envelope (point : UnitInterval) :
    (DistributionFunction.ofUpperBounds (fun _ : Unit => unitZero)
      (fun _ => unitZero)).function point = unitOne :=
  DistributionFunction.ofUpperBounds_of_inactive _ _ point
    (fun _ => point.property.1)

/-- Refutes automatic interpolation of a bound at threshold zero.
Because threshold zero is never active, the construction evaluates to one at
zero instead of the supplied bound zero. -/
public theorem zero_threshold_not_recovered :
    (DistributionFunction.ofUpperBounds (fun _ : Unit => unitZero)
      (fun _ => unitZero)).function unitZero ≠ unitZero := by
  rw [zero_threshold_envelope]
  intro equal
  exact Dedekind.one_ne_zero (congrArg Subtype.val equal)

/-- Empty indexing produces the constant-one distribution function.
No thresholds are active, so the infimum defaults to one everywhere.
Yields the Dirac point mass at zero when converted to a probability measure. -/
public theorem empty_bounds (thresholds bounds : Empty → UnitInterval)
    (point : UnitInterval) :
    (DistributionFunction.ofUpperBounds thresholds bounds).function point = unitOne :=
  DistributionFunction.ofUpperBounds_of_inactive _ _ point (fun index => Empty.elim index)

end Problib.Measure.Necessity.Distribution
