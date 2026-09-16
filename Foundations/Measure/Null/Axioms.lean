import Foundations.Measure.Null
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Measure.null_empty,
  Foundations.Measure.Measure.NullSet.mono,
  Foundations.Measure.Measure.NullSet.union,
  Foundations.Measure.Measure.NullSet.iUnion,
  Foundations.Measure.Measure.null_union_iff,
  Foundations.Measure.Measure.null_iUnion_iff,
  Foundations.Measure.Measure.measure_eq_of_null_difference,
  Foundations.Measure.Measure.exists_measurable_superset_lt,
  Foundations.Measure.Measure.NullSet.exists_measurable_superset
]

#audit_registered_claims

#audit_package [Foundations.Measure.Null] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
