import Problib.Measure.Outer
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.OuterMeasure.ext,
  Problib.Measure.OuterMeasure.empty_apply,
  Problib.Measure.OuterMeasure.mono_apply,
  Problib.Measure.OuterMeasure.iUnion_apply_le,
  Problib.Measure.OuterMeasure.union_apply_le,
  Problib.Measure.OuterMeasure.partition_apply_le,
  Problib.Measure.OuterMeasure.ofFunction_apply,
  Problib.Measure.OuterMeasure.ofFunction_le,
  Problib.Measure.OuterMeasure.le_ofFunction_apply,
  Problib.Measure.OuterMeasure.le_ofFunction,
  Problib.Measure.OuterMeasure.ofFunction_eq
]

#audit_registered_claims

#audit_package [Problib.Measure.Outer] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
