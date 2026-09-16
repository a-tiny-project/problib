import Foundations.Measure.Caratheodory
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.OuterMeasure.isCaratheodory_iff_reverse,
  Foundations.Measure.OuterMeasure.isCaratheodory_empty,
  Foundations.Measure.OuterMeasure.isCaratheodory_complement,
  Foundations.Measure.OuterMeasure.isCaratheodory_union,
  Foundations.Measure.OuterMeasure.isCaratheodory_inter,
  Foundations.Measure.OuterMeasure.isCaratheodory_difference,
  Foundations.Measure.OuterMeasure.isCaratheodory_prefixUnion,
  Foundations.Measure.OuterMeasure.partialSum_inter_eq,
  Foundations.Measure.OuterMeasure.inter_iUnion_apply,
  Foundations.Measure.OuterMeasure.iUnion_eq_of_caratheodory,
  Foundations.Measure.OuterMeasure.isCaratheodory_iUnion_of_disjoint,
  Foundations.Measure.OuterMeasure.isCaratheodory_disjointed,
  Foundations.Measure.OuterMeasure.isCaratheodory_iUnion,
  Foundations.Measure.OuterMeasure.caratheodory_measurable_iff,
  Foundations.Measure.OuterMeasure.ofFunction_caratheodory
]

#audit_registered_claims

#audit_package [Foundations.Measure.Caratheodory] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
