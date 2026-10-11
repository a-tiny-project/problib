import Problib.Measure.Additive.Comap.Finite
import Problib.Measure.Additive.Comap.Sum
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Measure.coproduct_decomposition,
  Problib.Measure.Measure.comap,
  Problib.Measure.Measure.comap_apply,
  Problib.Measure.Measure.comap_apply_univ,
  Problib.Measure.Measure.comap_id,
  Problib.Measure.Measure.comap_comp,
  Problib.Measure.Measure.comap_map,
  Problib.Measure.Measure.map_comap,
  Problib.Measure.Measure.map_comap_of_complement_null,
  Problib.Measure.Measure.comap_zero,
  Problib.Measure.Measure.comap_add,
  Problib.Measure.Measure.comap_smul,
  Problib.Measure.Measure.comap_sum,
  Problib.Measure.Measure.comap_restrict,
  Problib.Measure.Measure.comap_le_comap,
  Problib.Measure.Measure.comap_equivalence,
  Problib.Measure.Measure.map_comap_equivalence,
  Problib.Measure.Measure.IsFinite.comap,
  Problib.Measure.Measure.SigmaFinite.comap,
  Problib.Measure.Measure.SFinite.comap,
  Problib.Measure.Measure.comap_probability_iff,
  Problib.Measure.Measure.IsProbability.comap
]

#audit_registered_claims

#audit_package [Problib.Measure.Additive.Comap] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
