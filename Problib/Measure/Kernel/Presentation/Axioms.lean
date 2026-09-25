import Problib.Measure.Kernel.Presentation
import Problib.Measure.Kernel.Presentation.Fiber
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.section_measurable,
  Problib.Measure.Kernel.Presents,
  Problib.Measure.Kernel.Presentation,
  Problib.Measure.Kernel.Presentation.identity,
  Problib.Measure.Kernel.Presentation.attached,
  Problib.Measure.Kernel.integral_map,
  Problib.Measure.Kernel.real_integral_map,
  Problib.Measure.Kernel.presents_const_iff,
  Problib.Measure.Kernel.imageReference_apply,
  Problib.Measure.Kernel.fiberDensity_measurable,
  Problib.Measure.Kernel.density_map_of_fiber,
  Problib.Measure.Kernel.FiberReference.identity_isMarkov,
  Problib.Measure.Kernel.FiberReference.ofStandardBorel_isMarkov
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Presentation,
  Problib.Measure.Kernel.Presentation.Fiber] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
