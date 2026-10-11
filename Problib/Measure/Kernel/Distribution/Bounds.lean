module

public import Problib.Measure.Kernel.Distribution
public import Problib.Measure.Distribution.Bounds.Measurable

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real
open Problib.Measure.Real

universe u
variable {α : Type u} {source : Space α}

public section

/-- Constructs a probability kernel from countable parameter upper bounds.
Takes fixed unit-interval thresholds and measurable parameter bounds.
Produces a measurable family of probability measures on the unit interval. -/
@[expose] noncomputable def ofDistributionBounds (thresholds : Nat → UnitInterval)
    (bounds : Nat → α → UnitInterval)
    (measurable : ∀ index, MeasurableMap source unitBorel (bounds index)) :
    Kernel source unitBorel :=
  ofDistributionFunction
    (fun input => DistributionFunction.ofUpperBounds thresholds (fun index => bounds index input))
    (DistributionFunction.ofUpperBounds_measurable thresholds bounds measurable)

/-- Every fiber measure in the constructed kernel is a probability measure.
Total mass equals one on every parameter fiber. -/
theorem ofDistributionBounds_isProbability (thresholds : Nat → UnitInterval)
    (bounds : Nat → α → UnitInterval)
    (measurable : ∀ index, MeasurableMap source unitBorel (bounds index)) (input : α) :
    Measure.IsProbability (ofDistributionBounds thresholds bounds measurable input) :=
  ofDistributionFunction_isProbability _ _ input

/-- Proves the constructed kernel is finite.
The kernel has uniform bound one across all parameter fibers. -/
theorem ofDistributionBounds_isFinite (thresholds : Nat → UnitInterval)
    (bounds : Nat → α → UnitInterval)
    (measurable : ∀ index, MeasurableMap source unitBorel (bounds index)) :
    IsFinite (ofDistributionBounds thresholds bounds measurable) :=
  ofDistributionFunction_isFinite _ _

/-- Exact initial-interval masses for the constructed kernel.
Evaluates the kernel mass on `[0, point]` as the real value of the
constructed distribution function embedded into `ENNReal`. -/
theorem ofDistributionBounds_initial (thresholds : Nat → UnitInterval)
    (bounds : Nat → α → UnitInterval)
    (measurable : ∀ index, MeasurableMap source unitBorel (bounds index))
    (input : α) (point : UnitInterval) :
    ofDistributionBounds thresholds bounds measurable input (unitInitial point) =
      ENNReal.ofReal ((DistributionFunction.ofUpperBounds thresholds
        (fun index => bounds index input)).function point).val :=
  ofDistributionFunction_initial _ _ input point

/-- Active upper bounds on initial-interval kernel masses.
When point is strictly below a threshold, the initial-interval mass is bounded
above by the parameter bound in `ENNReal`. -/
theorem ofDistributionBounds_initial_le (thresholds : Nat → UnitInterval)
    (bounds : Nat → α → UnitInterval)
    (measurable : ∀ index, MeasurableMap source unitBorel (bounds index))
    (input : α) (point : UnitInterval) (index : Nat)
    (active : Construction.Dedekind.lt point.val (thresholds index).val) :
    ENNReal.le (ofDistributionBounds thresholds bounds measurable input (unitInitial point))
      (ENNReal.ofReal (bounds index input).val) := by
  rw [ofDistributionBounds_initial]
  exact ENNReal.ofReal_monotone (DistributionFunction.ofUpperBounds_le thresholds
    (fun index => bounds index input) point index active)

/-- Coherent recovery of a measurable family of distribution functions.
Recovers the distribution kernel when bounds match an existing measurable
family and thresholds are right-dense. -/
theorem ofDistributionBounds_eq (family : α → DistributionFunction)
    (slices : ∀ point, MeasurableMap source unitBorel (fun input => (family input).function point))
    (thresholds : Nat → UnitInterval)
    (dense : ∀ point right : UnitInterval, Construction.Dedekind.lt point.val right.val →
      ∃ index, Construction.Dedekind.lt point.val (thresholds index).val ∧
        Construction.Dedekind.le (thresholds index).val right.val) :
    ofDistributionBounds thresholds (fun index input => (family input).function (thresholds index))
      (fun index => slices (thresholds index)) = ofDistributionFunction family slices := by
  apply Kernel.ext
  intro input
  change (DistributionFunction.ofUpperBounds thresholds
    (fun index => (family input).function (thresholds index))).measure = (family input).measure
  rw [DistributionFunction.ofUpperBounds_eq (family input) thresholds dense]

end

end Problib.Measure.Kernel
