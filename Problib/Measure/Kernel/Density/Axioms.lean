import Problib.Measure.Kernel.Density
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.jointly_measurable_slice,
  Problib.Measure.Kernel.withDensity_apply,
  Problib.Measure.Kernel.withDensity_apply_set,
  Problib.Measure.Kernel.lintegral_withDensity,
  Problib.Measure.Kernel.withDensity_congr,
  Problib.Measure.Kernel.withDensity_sum,
  Problib.Measure.Kernel.withDensity_tsum,
  Problib.Measure.Kernel.IsFinite.withDensity_of_bounded,
  Problib.Measure.Kernel.IsFinite.withDensity,
  Problib.Measure.Kernel.IsSFinite.withDensity
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Density] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
