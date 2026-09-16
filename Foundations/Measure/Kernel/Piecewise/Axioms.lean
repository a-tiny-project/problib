import Foundations.Measure.Kernel.Piecewise
import Foundations.Measure.Kernel.Piecewise.Countable
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.countablePiecewise,
  Foundations.Measure.Kernel.countablePiecewise_apply,
  Foundations.Measure.Kernel.countablePiecewise_sum,
  Foundations.Measure.Kernel.countablePiecewise_eq_sum_piecewise,
  Foundations.Measure.Kernel.IsFinite.countablePiecewise,
  Foundations.Measure.Kernel.IsSFinite.countablePiecewise,
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
