import Problib.Measure.Null
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Measure.null_empty,
  Problib.Measure.Measure.NullSet.mono,
  Problib.Measure.Measure.NullSet.union,
  Problib.Measure.Measure.NullSet.iUnion,
  Problib.Measure.Measure.null_union_iff,
  Problib.Measure.Measure.null_iUnion_iff,
  Problib.Measure.Measure.measure_eq_of_null_difference,
  Problib.Measure.Measure.exists_measurable_superset_lt,
  Problib.Measure.Measure.NullSet.exists_measurable_superset
]

#audit_registered_claims

#audit_package [Problib.Measure.Null] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
