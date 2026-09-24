import Problib.Measure.Kernel.Piecewise
import Problib.Measure.Kernel.Piecewise.Countable
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.countablePiecewise,
  Problib.Measure.Kernel.countablePiecewise_apply,
  Problib.Measure.Kernel.countablePiecewise_sum,
  Problib.Measure.Kernel.countablePiecewise_eq_sum_piecewise,
  Problib.Measure.Kernel.IsFinite.countablePiecewise,
  Problib.Measure.Kernel.IsSFinite.countablePiecewise,
  Problib.Measure.Kernel.piecewise,
  Problib.Measure.Kernel.piecewise_apply_of_mem,
  Problib.Measure.Kernel.piecewise_apply_of_not_mem,
  Problib.Measure.Kernel.piecewise_sum,
  Problib.Measure.Kernel.IsFinite.piecewise,
  Problib.Measure.Kernel.IsSFinite.piecewise
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Piecewise] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
