import Problib.Measure.Dynkin
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.PiSystem.measurable,
  Problib.Measure.DynkinSystem.ext,
  Problib.Measure.DynkinSystem.univ,
  Problib.Measure.DynkinSystem.union,
  Problib.Measure.DynkinSystem.difference,
  Problib.Measure.DynkinSystem.generated_contains,
  Problib.Measure.DynkinSystem.generated_minimal,
  Problib.Measure.DynkinSystem.generated_measurable,
  Problib.Measure.DynkinSystem.generated_intersection,
  Problib.Measure.DynkinSystem.pi_lambda,
  Problib.Measure.Measure.ext_of_generate
]

#audit_registered_claims

#audit_package [Problib.Measure.Dynkin] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
