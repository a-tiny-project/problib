import Foundations.Measure.Kernel.Measurable
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.verticalMap_measurable,
  Foundations.Measure.Kernel.verticalSection_measurable,
  Foundations.Measure.Kernel.section_apply_measurable_of_finite_fibers,
  Foundations.Measure.Kernel.section_apply_measurable,
  Foundations.Measure.Kernel.lintegral_measurable,
  Foundations.Measure.Kernel.lintegral_measurable_joint
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Measurable] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
