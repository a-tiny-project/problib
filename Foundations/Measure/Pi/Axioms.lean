import Foundations.Measure.Pi
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Space.PiGenerator,
  Foundations.Measure.Space.pi,
  Foundations.Measure.Space.coordinate_measurable,
  Foundations.Measure.Space.pi_measurable,
  Foundations.Measure.Space.pi_measurable_iff,
  Foundations.Measure.Space.pi_map,
  Foundations.Measure.Space.pi_reindex
]

#audit_registered_claims

#audit_package [Foundations.Measure.Pi] allowing [propext, Quot.sound, Classical.choice]
