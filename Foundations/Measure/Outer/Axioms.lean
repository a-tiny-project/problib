import Foundations.Measure.Outer
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.OuterMeasure.ext,
  Foundations.Measure.OuterMeasure.empty_apply,
  Foundations.Measure.OuterMeasure.mono_apply,
  Foundations.Measure.OuterMeasure.iUnion_apply_le,
  Foundations.Measure.OuterMeasure.union_apply_le,
  Foundations.Measure.OuterMeasure.partition_apply_le,
  Foundations.Measure.OuterMeasure.ofFunction_apply,
  Foundations.Measure.OuterMeasure.ofFunction_le,
  Foundations.Measure.OuterMeasure.le_ofFunction_apply,
  Foundations.Measure.OuterMeasure.le_ofFunction,
  Foundations.Measure.OuterMeasure.ofFunction_eq
]

#audit_registered_claims

#audit_package [Foundations.Measure.Outer] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
