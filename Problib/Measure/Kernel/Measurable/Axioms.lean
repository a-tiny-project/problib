import Problib.Measure.Kernel.Measurable
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.vertical_map_measurable,
  Problib.Measure.Kernel.verticalSection_measurable,
  Problib.Measure.Kernel.section_apply_measurable_of_finite_fibers,
  Problib.Measure.Kernel.section_apply_measurable,
  Problib.Measure.Kernel.lintegral_measurable,
  Problib.Measure.Kernel.lintegral_measurable_joint
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Measurable] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
