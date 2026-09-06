import Foundations.Measure.Kernel.Piecewise
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.piecewise,
  Foundations.Measure.Kernel.piecewise_apply_of_mem,
  Foundations.Measure.Kernel.piecewise_apply_of_not_mem,
  Foundations.Measure.Kernel.piecewise_sum,
  Foundations.Measure.Kernel.IsFinite.piecewise,
  Foundations.Measure.Kernel.IsSFinite.piecewise
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Piecewise] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
