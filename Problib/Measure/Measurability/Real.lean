module

public import Problib.Measure.Measurability.Extended
public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Real.Order

/-! `measurability` rules for real-valued maps.

The arithmetic combinators are stated in composed form, such as
`fun x => add (left x) (right x)`, so `apply` unifies them by pattern and
recurses into both arguments. Negation, the reciprocal, and the conversions
between reals and extended reals are closed maps that composition uses as its
outer map. The order comparisons close the region premise of
`MeasurableMap.ite`, so a choice on `le (f x) (g x)` splits all the way down.
-/

macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.Real.translate_measurable)
macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.Real.toReal_measurable)
macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.Real.ofReal_measurable)
macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.Real.inverse_measurable)
macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.Real.neg_measurable)

macro_rules
  | `(tactic| measurability_split) => `(tactic|
      (measurability_target Problib.Measure.Real.borel
       first
       | (measurability_apply Problib.Measure.Real.measurable_add <;> measurability_core)
       | (measurability_apply Problib.Measure.Real.measurable_sub <;> measurability_core)
       | (measurability_apply Problib.Measure.Real.measurable_mul <;> measurability_core)
       | (measurability_apply Problib.Measure.Real.measurable_div <;> measurability_core)))
macro_rules
  | `(tactic| measurability_split) => `(tactic|
      (measurability_goal Problib.Measure.Space.Measurable
       first
       | (measurability_apply Problib.Measure.Real.measurable_le <;> measurability_core)
       | (measurability_apply Problib.Measure.Real.measurable_lt <;> measurability_core)))
