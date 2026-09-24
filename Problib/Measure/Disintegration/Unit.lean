module

public import Problib.Measure.Disintegration.Reconstruction
public import Problib.Measure.Disintegration.Unit.Reconstruction

set_option autoImplicit false

namespace Problib.Measure.Measure.Disintegration

open Problib.Measure.Real

universe u

variable {beta : Type u} {target : Space beta}

/-- Construct a disintegration package for a joint measure on the unit interval
times an arbitrary measurable parameter space from a sigma-finite second
marginal. -/
@[expose] public noncomputable def ofUnit
    (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) : Disintegration joint where
  conditional := UnitDisintegration.conditional joint finite
  conditionalSFinite := (UnitDisintegration.conditional_isFinite joint finite).toSFinite
  reconstruction := UnitDisintegration.conditional_reconstruct joint finite

/-- The conditional distribution kernel constructed by ofUnit is a probability
measure on every parameter fiber including exceptional null fibers. -/
public theorem ofUnit_isProbability
    (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) (input : beta) :
    IsProbability ((ofUnit joint finite).conditional input) :=
  UnitDisintegration.conditional_isProbability joint finite input

end Problib.Measure.Measure.Disintegration
