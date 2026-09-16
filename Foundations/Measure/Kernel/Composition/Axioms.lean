import Foundations.Measure.Kernel.Composition
import Foundations.Measure.Kernel.Composition.Piecewise
import Foundations.Measure.Kernel.Composition.Necessity
import Foundations.Measure.Kernel.Composition.Transport
import Foundations.Measure.Kernel.Composition.Bind.Transport
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Measure.bind_copair,
  Foundations.Measure.Measure.bind_comap_inl,
  Foundations.Measure.Measure.bind_comap_inr,
  Foundations.Measure.Kernel.copair_comp,
  Foundations.Measure.Kernel.comp_copair,
  Foundations.Measure.Kernel.comp_copair_zero,
  Foundations.Measure.Kernel.comp_zero_copair,
  Foundations.Measure.Kernel.countablePiecewise_comp,
  Foundations.Measure.Kernel.Composition.Necessity.source_comap_bind_needs_support,
  Foundations.Measure.Kernel.Composition.Necessity.sum_source_comap_bind_needs_support,
  Foundations.Measure.Kernel.precomp_comp_kernel,
  Foundations.Measure.Kernel.map_comp,
  Foundations.Measure.Kernel.comp_map,
  Foundations.Measure.Kernel.comp_comap,
  Foundations.Measure.Kernel.comap_comp_of_zero_outside,
  Foundations.Measure.Kernel.comap_comp_of_complement_null,
  Foundations.Measure.Measure.bind_map,
  Foundations.Measure.Measure.map_bind,
  Foundations.Measure.Measure.comap_bind,
  Foundations.Measure.Measure.bind_comap,
  Foundations.Measure.Measure.bind_comap_of_zero_outside,
  Foundations.Measure.Measure.bind_comap_of_complement_null,
  Foundations.Measure.Measure.zero_bind,
  Foundations.Measure.Measure.bind_zero,
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
