import Problib.Measure.Kernel.Composition
import Problib.Measure.Kernel.Composition.Piecewise
import Problib.Measure.Kernel.Composition.Necessity
import Problib.Measure.Kernel.Composition.Transport
import Problib.Measure.Kernel.Composition.Bind.Transport
import Problib.Measure.Kernel.Composition.Bind.Deficit
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Measure.bind_copair,
  Problib.Measure.Measure.bind_comap_inl,
  Problib.Measure.Measure.bind_comap_inr,
  Problib.Measure.Kernel.copair_comp,
  Problib.Measure.Kernel.comp_copair,
  Problib.Measure.Kernel.comp_copair_zero,
  Problib.Measure.Kernel.comp_zero_copair,
  Problib.Measure.Kernel.countablePiecewise_comp,
  Problib.Measure.Kernel.Composition.Necessity.source_comap_bind_needs_support,
  Problib.Measure.Kernel.Composition.Necessity.sum_source_comap_bind_needs_support,
  Problib.Measure.Kernel.precomp_comp_kernel,
  Problib.Measure.Kernel.map_comp,
  Problib.Measure.Kernel.comp_map,
  Problib.Measure.Kernel.comp_comap,
  Problib.Measure.Kernel.comap_comp_of_zero_outside,
  Problib.Measure.Kernel.comap_comp_of_complement_null,
  Problib.Measure.Measure.bind_map,
  Problib.Measure.Measure.map_bind,
  Problib.Measure.Measure.comap_bind,
  Problib.Measure.Measure.bind_comap,
  Problib.Measure.Measure.bind_comap_of_zero_outside,
  Problib.Measure.Measure.bind_comap_of_complement_null,
  Problib.Measure.Measure.zero_bind,
  Problib.Measure.Measure.bind_zero,
  Problib.Measure.Measure.add_bind,
  Problib.Measure.Measure.smul_bind,
  Problib.Measure.Measure.IsProbability.bind,
  Problib.Measure.Measure.bind_deficit_le,
  Problib.Measure.Measure.bind,
  Problib.Measure.Measure.bind_apply,
  Problib.Measure.Measure.lintegral_bind,
  Problib.Measure.Measure.bind_const,
  Problib.Measure.Measure.dirac_bind,
  Problib.Measure.Measure.bind_deterministic,
  Problib.Measure.Measure.bind_sum_left,
  Problib.Measure.Measure.bind_sum_right,
  Problib.Measure.Measure.SFinite.bind,
  Problib.Measure.Kernel.comp,
  Problib.Measure.Kernel.comp_apply,
  Problib.Measure.Kernel.comp_apply_measurable,
  Problib.Measure.Kernel.lintegral_comp,
  Problib.Measure.Measure.bind_assoc,
  Problib.Measure.Measure.IsFinite.bind,
  Problib.Measure.Kernel.comp_assoc,
  Problib.Measure.Kernel.const_comp,
  Problib.Measure.Kernel.deterministic_comp_apply,
  Problib.Measure.Kernel.comp_deterministic,
  Problib.Measure.Kernel.IsFinite.comp,
  Problib.Measure.Kernel.IsSFinite.comp
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Composition] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
