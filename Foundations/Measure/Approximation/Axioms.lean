import Foundations.Measure.Approximation
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Space.symmDiff_measurable,
  Foundations.Measure.Measure.setDistance,
  Foundations.Measure.Measure.setDistance_self,
  Foundations.Measure.Measure.setDistance_comm,
  Foundations.Measure.Measure.setDistance_complement,
  Foundations.Measure.Measure.setDistance_triangle,
  Foundations.Measure.Measure.setDistance_union,
  Foundations.Measure.Measure.le_add_setDistance,
  Foundations.Measure.Measure.Approximable,
  Foundations.Measure.Measure.Approximable.member,
  Foundations.Measure.Measure.Approximable.empty,
  Foundations.Measure.Measure.Approximable.complement,
  Foundations.Measure.Measure.Approximable.union,
  Foundations.Measure.Measure.Approximable.prefixUnion,
  Foundations.Measure.Measure.Approximable.iUnion,
  Foundations.Measure.Measure.approximable_of_measurable
]

#audit_registered_claims

#audit_package [Foundations.Measure.Approximation] allowing [propext, Quot.sound, Classical.choice]
