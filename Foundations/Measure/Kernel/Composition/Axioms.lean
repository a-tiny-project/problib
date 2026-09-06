import Foundations.Measure.Kernel.Composition
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Measure.zero_bind,
  Foundations.Measure.Measure.add_bind,
  Foundations.Measure.Measure.smul_bind,
  Foundations.Measure.Measure.IsProbability.bind,
  Foundations.Measure.Measure.bind,
  Foundations.Measure.Measure.bind_apply,
  Foundations.Measure.Measure.lintegral_bind,
  Foundations.Measure.Measure.bind_const,
  Foundations.Measure.Measure.dirac_bind,
  Foundations.Measure.Measure.bind_deterministic,
  Foundations.Measure.Measure.bind_sum_left,
  Foundations.Measure.Measure.bind_sum_right,
  Foundations.Measure.Measure.SFinite.bind,
  Foundations.Measure.Kernel.comp,
  Foundations.Measure.Kernel.comp_apply,
  Foundations.Measure.Kernel.comp_apply_measurable,
  Foundations.Measure.Kernel.lintegral_comp,
  Foundations.Measure.Measure.bind_assoc,
  Foundations.Measure.Measure.IsFinite.bind,
  Foundations.Measure.Kernel.comp_assoc,
  Foundations.Measure.Kernel.const_comp,
  Foundations.Measure.Kernel.deterministic_comp_apply,
  Foundations.Measure.Kernel.comp_deterministic,
  Foundations.Measure.Kernel.IsFinite.comp,
  Foundations.Measure.Kernel.IsSFinite.comp
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Composition] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
