import Foundations.Measure.Dynkin
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.PiSystem.measurable,
  Foundations.Measure.DynkinSystem.ext,
  Foundations.Measure.DynkinSystem.univ,
  Foundations.Measure.DynkinSystem.union,
  Foundations.Measure.DynkinSystem.difference,
  Foundations.Measure.DynkinSystem.generated_contains,
  Foundations.Measure.DynkinSystem.generated_minimal,
  Foundations.Measure.DynkinSystem.generated_measurable,
  Foundations.Measure.DynkinSystem.generated_intersection,
  Foundations.Measure.DynkinSystem.pi_lambda,
  Foundations.Measure.Measure.ext_of_generate
]

#audit_registered_claims

#audit_package [Foundations.Measure.Dynkin] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
