module

public import Problib.Measure.Real.Borel

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction

public section

/-- A cumulative distribution function on the closed unit interval `[0, 1]`.
Requires monotonicity, normalization to one at the upper endpoint, and an
order-witness formulation of right-continuity. Admits an atom at zero.
No measure, kernel, integral, or selector is assumed as an input field. -/
structure DistributionFunction where
  function : UnitInterval → UnitInterval
  monotone : ∀ {left right}, Dedekind.le left.val right.val →
    Dedekind.le (function left).val (function right).val
  upper : function unitOne = unitOne
  /-- Order-witness formulation of right-continuity: whenever `upper` strictly
  exceeds `function point` and `point < 1`, there exists a point `right > point`
  such that `function right < upper`. -/
  right_continuous : ∀ point, Dedekind.lt point.val Dedekind.one →
    ∀ upper, Dedekind.lt (function point).val upper →
      ∃ right, Dedekind.lt point.val right.val ∧ Dedekind.lt (function right).val upper

/-- Extensional equality for distribution functions.
Two distributions are equal when their carrier functions agree everywhere. -/
@[ext] theorem DistributionFunction.ext {left right : DistributionFunction}
    (same : left.function = right.function) : left = right := by
  cases left
  cases right
  cases same
  rfl

theorem DistributionFunction.function_measurable (distribution : DistributionFunction) :
    MeasurableMap unitBorel unitBorel distribution.function :=
  unit_monotone_measurable (fun included => distribution.monotone included)

/-- In combination with monotonicity, the right-continuity order witness proves
ordinary two-sided bounds on a right-neighborhood `[point, right]`. -/
theorem DistributionFunction.right_continuous_bounds (distribution : DistributionFunction)
    (point : UnitInterval) (room : Dedekind.lt point.val Dedekind.one)
    (lower upper : Carrier)
    (lowerBound : Dedekind.lt lower (distribution.function point).val)
    (upperBound : Dedekind.lt (distribution.function point).val upper) :
    ∃ right : UnitInterval, Dedekind.lt point.val right.val ∧
      ∀ input : UnitInterval, Dedekind.le point.val input.val →
        Dedekind.le input.val right.val →
        Dedekind.lt lower (distribution.function input).val ∧
        Dedekind.lt (distribution.function input).val upper := by
  rcases distribution.right_continuous point room upper upperBound with
    ⟨right, rightAbove, rightBelow⟩
  refine ⟨right, rightAbove, ?_⟩
  intro input above below
  exact ⟨Dedekind.lt_of_lt_of_le lowerBound (distribution.monotone above),
    Dedekind.lt_of_le_of_lt (distribution.monotone below) rightBelow⟩

end

end Problib.Measure.Real
