import Problib.Measure.Caratheodory
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.OuterMeasure.isCaratheodory_iff_reverse,
  Problib.Measure.OuterMeasure.isCaratheodory_empty,
  Problib.Measure.OuterMeasure.isCaratheodory_complement,
  Problib.Measure.OuterMeasure.isCaratheodory_union,
  Problib.Measure.OuterMeasure.isCaratheodory_inter,
  Problib.Measure.OuterMeasure.isCaratheodory_difference,
  Problib.Measure.OuterMeasure.isCaratheodory_prefixUnion,
  Problib.Measure.OuterMeasure.partialSum_inter_eq,
  Problib.Measure.OuterMeasure.inter_iUnion_apply,
  Problib.Measure.OuterMeasure.iUnion_eq_of_caratheodory,
  Problib.Measure.OuterMeasure.isCaratheodory_iUnion_of_disjoint,
  Problib.Measure.OuterMeasure.isCaratheodory_disjointed,
  Problib.Measure.OuterMeasure.isCaratheodory_iUnion,
  Problib.Measure.OuterMeasure.caratheodory_measurable_iff,
  Problib.Measure.OuterMeasure.ofFunction_caratheodory
]

#audit_registered_claims

#audit_package [Problib.Measure.Caratheodory] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
