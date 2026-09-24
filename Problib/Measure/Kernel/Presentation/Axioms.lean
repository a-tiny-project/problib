import Problib.Measure.Kernel.Presentation
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.section_measurable,
  Problib.Measure.Kernel.Presents,
  Problib.Measure.Kernel.Presentation,
  Problib.Measure.Kernel.Presentation.identity,
  Problib.Measure.Kernel.Presentation.attached,
  Problib.Measure.Kernel.integral_map,
  Problib.Measure.Kernel.real_integral_map,
  Problib.Measure.Kernel.presents_const_iff
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Presentation] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
