import Problib.Measure.Kernel.Basic
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.ext,
  Problib.Measure.Kernel.ext_measurable,
  Problib.Measure.Kernel.const_apply,
  Problib.Measure.Kernel.deterministic_apply,
  Problib.Measure.Kernel.map_apply,
  Problib.Measure.Kernel.zero_apply,
  Problib.Measure.Kernel.add_apply,
  Problib.Measure.Kernel.sum_apply,
  Problib.Measure.Kernel.sum_add,
  Problib.Measure.Kernel.sum_double,
  Problib.Measure.Kernel.map_sum,
  Problib.Measure.Kernel.IsFinite.measure,
  Problib.Measure.Kernel.IsFinite.const,
  Problib.Measure.Kernel.IsFinite.deterministic,
  Problib.Measure.Kernel.IsFinite.zero,
  Problib.Measure.Kernel.IsFinite.add,
  Problib.Measure.Kernel.IsFinite.map,
  Problib.Measure.Kernel.IsFinite.toSFinite,
  Problib.Measure.Kernel.IsSFinite.ofFinite,
  Problib.Measure.Kernel.IsSFinite.zero,
  Problib.Measure.Kernel.IsSFinite.deterministic,
  Problib.Measure.Kernel.IsSFinite.add,
  Problib.Measure.Kernel.IsSFinite.sum,
  Problib.Measure.Kernel.IsSFinite.map,
  Problib.Measure.Kernel.IsSFinite.const,
  Problib.Measure.Kernel.IsSFinite.measure
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Basic] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
