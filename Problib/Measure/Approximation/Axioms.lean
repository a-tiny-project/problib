import Problib.Measure.Approximation
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Space.symmDiff_measurable,
  Problib.Measure.Measure.setDistance,
  Problib.Measure.Measure.setDistance_self,
  Problib.Measure.Measure.setDistance_comm,
  Problib.Measure.Measure.setDistance_complement,
  Problib.Measure.Measure.setDistance_triangle,
  Problib.Measure.Measure.setDistance_union,
  Problib.Measure.Measure.le_add_setDistance,
  Problib.Measure.Measure.Approximable,
  Problib.Measure.Measure.Approximable.member,
  Problib.Measure.Measure.Approximable.empty,
  Problib.Measure.Measure.Approximable.complement,
  Problib.Measure.Measure.Approximable.union,
  Problib.Measure.Measure.Approximable.prefixUnion,
  Problib.Measure.Measure.Approximable.iUnion,
  Problib.Measure.Measure.approximable_of_measurable
]

#audit_registered_claims

#audit_package [Problib.Measure.Approximation] allowing [propext, Quot.sound, Classical.choice]
