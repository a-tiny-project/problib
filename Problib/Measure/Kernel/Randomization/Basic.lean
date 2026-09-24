module

public import Problib.Measure.Kernel.Basic
public import Problib.Measure.Product
public import Problib.Measure.Uniform

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Measure.Real Problib.Real

universe u v w

public section

variable {alpha : Type u} {beta : Type v} {gamma : Type w}
  {source : Space alpha} {target : Space beta} {result : Space gamma}

/-- Packages a jointly measurable function from parameter and Uniform seed
that pushes the standard Uniform measure to the kernel fiber on every input. -/
structure Randomizer (kernel : Kernel source target) where
  function : alpha × UnitInterval → beta
  measurable : MeasurableMap (Space.product source unitBorel) target function
  law : ∀ input, uniform01.map (fun seed => function (input, seed))
    (MeasurableMap.comp measurable (Space.pair_measurable
      (MeasurableMap.constant unitBorel source input) (MeasurableMap.identity unitBorel))) = kernel input

namespace Randomizer

/-- For each parameter input, the fiber map from the Uniform seed to the target is measurable. -/
theorem fiber_measurable {kernel : Kernel source target}
    (selection : Randomizer kernel) (input : alpha) :
    MeasurableMap unitBorel target (fun seed => selection.function (input, seed)) :=
  MeasurableMap.comp selection.measurable (Space.pair_measurable
    (MeasurableMap.constant unitBorel source input) (MeasurableMap.identity unitBorel))

/-- Every fiber of a randomizable kernel is a probability measure. -/
theorem isProbability {kernel : Kernel source target}
    (selection : Randomizer kernel) (input : alpha) : Measure.IsProbability (kernel input) := by
  rw [← selection.law input]
  exact uniform01_isProbability.map _ _

/-- Transports a randomizer along a measurable map to randomize the pushforward kernel. -/
@[expose] noncomputable def map {kernel : Kernel source target}
    (selection : Randomizer kernel) (function : beta → gamma)
    (measurable : MeasurableMap target result function) :
    Randomizer (kernel.map function measurable) where
  function := fun pair => function (selection.function pair)
  measurable := MeasurableMap.comp measurable selection.measurable
  law := by
    intro input
    change uniform01.map (fun seed => function (selection.function (input, seed))) _ =
      (kernel input).map function measurable
    rw [← Measure.map_comp uniform01 (fun seed => selection.function (input, seed))
      function (selection.fiber_measurable input) measurable, selection.law input]

end Randomizer

end

end Problib.Measure.Kernel
