import Problib.Measure.Pi
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Space.PiGenerator,
  Problib.Measure.Space.pi,
  Problib.Measure.Space.coordinate_measurable,
  Problib.Measure.Space.pi_measurable,
  Problib.Measure.Space.pi_measurable_iff,
  Problib.Measure.Space.pi_map,
  Problib.Measure.Space.pi_reindex
]

#audit_registered_claims

#audit_package [Problib.Measure.Pi] allowing [propext, Quot.sound, Classical.choice]
