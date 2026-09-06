module

public import Foundations.Measure.Space
public import Foundations.QuasiBorel.Space

set_option autoImplicit false

namespace Foundations.QuasiBorel

open Foundations.Measure

universe u v

variable {α : Type u} {β : Type v}

/-- Canonical quasi-Borel random source generated from an arbitrary measurable space.
Morphisms are measurable maps, and random partitions are measurable partitions into `Nat`. -/
@[expose] public def Source.ofMeasurable (space : Foundations.Measure.Space α) :
    Source α where
  Measurable := MeasurableMap space space
  Partition := fun partition => ∀ index,
    space.Measurable (fun value => partition value = index)
  identity := MeasurableMap.identity space
  constant := MeasurableMap.constant space space
  comp := fun firstMeasurable secondMeasurable =>
    MeasurableMap.comp secondMeasurable firstMeasurable
  partitionReparam := by
    intro partition reparam partitionMeasurable reparamMeasurable index
    exact reparamMeasurable (partitionMeasurable index)
  piecewise := MeasurableMap.countablePiecewise

/-- Canonical quasi-Borel space generated from explicit source and target measurable spaces.
Random curves are measurable maps from `source` to `target`. -/
@[expose] public def Space.ofMeasurable (source : Foundations.Measure.Space α)
    (target : Foundations.Measure.Space β) : Space (Source.ofMeasurable source) where
  Carrier := β
  Random := MeasurableMap source target
  constant := MeasurableMap.constant source target
  reparam := fun reparamMeasurable randomMeasurable =>
    MeasurableMap.comp randomMeasurable reparamMeasurable
  piecewise := MeasurableMap.countablePiecewise

end Foundations.QuasiBorel
