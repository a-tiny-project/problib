import Foundations.Measure.Kernel.Basic
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.ext,
  Foundations.Measure.Kernel.ext_measurable,
  Foundations.Measure.Kernel.const_apply,
  Foundations.Measure.Kernel.deterministic_apply,
  Foundations.Measure.Kernel.map_apply,
  Foundations.Measure.Kernel.zero_apply,
  Foundations.Measure.Kernel.add_apply,
  Foundations.Measure.Kernel.sum_apply,
  Foundations.Measure.Kernel.sum_add,
  Foundations.Measure.Kernel.sum_double,
  Foundations.Measure.Kernel.map_sum,
  Foundations.Measure.Kernel.IsFinite.measure,
  Foundations.Measure.Kernel.IsFinite.const,
  Foundations.Measure.Kernel.IsFinite.deterministic,
  Foundations.Measure.Kernel.IsFinite.zero,
  Foundations.Measure.Kernel.IsFinite.add,
  Foundations.Measure.Kernel.IsFinite.map,
  Foundations.Measure.Kernel.IsFinite.toSFinite,
  Foundations.Measure.Kernel.IsSFinite.ofFinite,
  Foundations.Measure.Kernel.IsSFinite.zero,
  Foundations.Measure.Kernel.IsSFinite.deterministic,
  Foundations.Measure.Kernel.IsSFinite.add,
  Foundations.Measure.Kernel.IsSFinite.sum,
  Foundations.Measure.Kernel.IsSFinite.map,
  Foundations.Measure.Kernel.IsSFinite.const,
  Foundations.Measure.Kernel.IsSFinite.measure
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Basic] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
