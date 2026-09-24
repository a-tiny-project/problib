import Problib.Measure.Kernel.Comap
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.comap,
  Problib.Measure.Kernel.comap_apply,
  Problib.Measure.Kernel.comap_apply_univ,
  Problib.Measure.Kernel.comap_id,
  Problib.Measure.Kernel.comap_comp,
  Problib.Measure.Kernel.comap_map,
  Problib.Measure.Kernel.map_comap_apply,
  Problib.Measure.Kernel.map_comap_of_complement_null,
  Problib.Measure.Kernel.comap_zero,
  Problib.Measure.Kernel.comap_add,
  Problib.Measure.Kernel.comap_sum,
  Problib.Measure.Kernel.comap_const,
  Problib.Measure.Kernel.comap_equivalence,
  Problib.Measure.Kernel.comap_probability_iff,
  Problib.Measure.Kernel.IsFinite.comap,
  Problib.Measure.Kernel.IsSFinite.comap
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Comap] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
