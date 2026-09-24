module

public import Problib.Measure.Space
public import Problib.QuasiBorel.Space

set_option autoImplicit false

namespace Problib.QuasiBorel

open Problib.Measure

universe u v

variable {α : Type u} {β : Type v}

/-- Canonical quasi-Borel random source generated from an arbitrary measurable space.
Morphisms are measurable maps, and random partitions are measurable partitions into `Nat`. -/
@[expose] public def Source.ofMeasurable (space : Problib.Measure.Space α) :
    Source α where
  Measurable := MeasurableMap space space
  Partition := fun partition => ∀ index,
    space.Measurable (fun value => partition value = index)
  identity := MeasurableMap.identity space
  constant := MeasurableMap.constant space space
  comp := fun firstMeasurable secondMeasurable =>
    MeasurableMap.comp secondMeasurable firstMeasurable
  partition_reparam := by
    intro partition reparam partitionMeasurable reparamMeasurable index
    exact reparamMeasurable (partitionMeasurable index)
  piecewise := MeasurableMap.countable_piecewise

/-- Canonical quasi-Borel space generated from explicit source and target measurable spaces.
Random curves are measurable maps from `source` to `target`. -/
@[expose] public def Space.ofMeasurable (source : Problib.Measure.Space α)
    (target : Problib.Measure.Space β) : Space (Source.ofMeasurable source) where
  Carrier := β
  Random := MeasurableMap source target
  constant := MeasurableMap.constant source target
  reparam := fun reparamMeasurable randomMeasurable =>
    MeasurableMap.comp randomMeasurable reparamMeasurable
  piecewise := MeasurableMap.countable_piecewise

end Problib.QuasiBorel
