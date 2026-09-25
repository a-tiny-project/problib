import Problib.Measure.Equivalence
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.MeasurableEquivalence.identity,
  Problib.Measure.MeasurableEquivalence.forward_injective,
  Problib.Measure.MeasurableEquivalence.inverse_injective,
  Problib.Measure.MeasurableEquivalence.symm,
  Problib.Measure.MeasurableEquivalence.trans
]

#audit_registered_claims

#audit_package [Problib.Measure.Equivalence] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
