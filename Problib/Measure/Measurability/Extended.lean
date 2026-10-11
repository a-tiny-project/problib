module

public import Problib.Measure.Measurability
public import Problib.Measure.Extended.Basic
public import Problib.Measure.Extended.Algebra

/-! `measurability` rules for `ENNRealMeasurable` goals.

An `ENNRealMeasurable` goal becomes a `MeasurableMap` goal into the extended
Borel space, or splits through composition, indicators, piecewise definitions,
products and sums. -/

macro_rules
  | `(tactic| measurability_split) => `(tactic|
      (measurability_target Problib.Measure.ennrealBorel
       measurability_apply Problib.Measure.ENNRealMeasurable.measurableMap
       measurability_core))
macro_rules
  | `(tactic| measurability_split) => `(tactic|
      (measurability_goal Problib.Measure.ENNRealMeasurable
       first
       | measurability_apply Problib.Measure.ENNRealMeasurable.constant
       | measurability_apply Problib.Measure.ENNRealMeasurable.identity
       | (measurability_apply Problib.Measure.ENNRealMeasurable.add <;> measurability_core)
       | (measurability_apply Problib.Measure.ENNRealMeasurable.mul <;> measurability_core)
       | (measurability_apply Problib.Measure.ENNRealMeasurable.piecewise <;> measurability_core)
       | (measurability_apply Problib.Measure.ENNRealMeasurable.indicator <;> measurability_core)
       | (measurability_apply Problib.Measure.ENNRealMeasurable.comp
          measurability_outer Problib.Measure.ENNRealMeasurable.comp
          measurability_core)))
