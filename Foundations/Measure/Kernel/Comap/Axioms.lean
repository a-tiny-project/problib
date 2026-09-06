import Foundations.Measure.Kernel.Comap
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.comap,
  Foundations.Measure.Kernel.comap_apply,
  Foundations.Measure.Kernel.comap_apply_univ,
  Foundations.Measure.Kernel.comap_id,
  Foundations.Measure.Kernel.comap_comp,
  Foundations.Measure.Kernel.comap_map,
  Foundations.Measure.Kernel.map_comap_apply,
  Foundations.Measure.Kernel.map_comap_of_complement_null,
  Foundations.Measure.Kernel.comap_zero,
  Foundations.Measure.Kernel.comap_add,
  Foundations.Measure.Kernel.comap_sum,
  Foundations.Measure.Kernel.comap_const,
  Foundations.Measure.Kernel.comap_equivalence,
  Foundations.Measure.Kernel.comap_probability_iff,
  Foundations.Measure.Kernel.IsFinite.comap,
  Foundations.Measure.Kernel.IsSFinite.comap
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Comap] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
