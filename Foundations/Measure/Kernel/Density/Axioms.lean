import Foundations.Measure.Kernel.Density
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.jointlyMeasurable_slice,
  Foundations.Measure.Kernel.withDensity_apply,
  Foundations.Measure.Kernel.withDensity_apply_set,
  Foundations.Measure.Kernel.lintegral_withDensity,
  Foundations.Measure.Kernel.withDensity_congr,
  Foundations.Measure.Kernel.withDensity_sum,
  Foundations.Measure.Kernel.withDensity_tsum,
  Foundations.Measure.Kernel.IsFinite.withDensity_of_bounded,
  Foundations.Measure.Kernel.IsFinite.withDensity,
  Foundations.Measure.Kernel.IsSFinite.withDensity
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Density] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
