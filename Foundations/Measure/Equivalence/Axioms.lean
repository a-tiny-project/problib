import Foundations.Measure.Equivalence
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.MeasurableEquivalence.identity,
  Foundations.Measure.MeasurableEquivalence.forward_injective,
  Foundations.Measure.MeasurableEquivalence.inverse_injective,
  Foundations.Measure.MeasurableEquivalence.symm,
  Foundations.Measure.MeasurableEquivalence.trans
]

#audit_registered_claims

#audit_package [Foundations.Measure.Equivalence] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
