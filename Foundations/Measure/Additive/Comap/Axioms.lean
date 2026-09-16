import Foundations.Measure.Additive.Comap.Finite
import Foundations.Measure.Additive.Comap.Sum
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Measure.coproduct_decomposition,
  Foundations.Measure.Measure.comap,
  Foundations.Measure.Measure.comap_apply,
  Foundations.Measure.Measure.comap_apply_univ,
  Foundations.Measure.Measure.comap_id,
  Foundations.Measure.Measure.comap_comp,
  Foundations.Measure.Measure.comap_map,
  Foundations.Measure.Measure.map_comap,
  Foundations.Measure.Measure.map_comap_of_complement_null,
  Foundations.Measure.Measure.comap_zero,
  Foundations.Measure.Measure.comap_add,
  Foundations.Measure.Measure.comap_smul,
  Foundations.Measure.Measure.comap_sum,
  Foundations.Measure.Measure.comap_restrict,
  Foundations.Measure.Measure.comap_le_comap,
  Foundations.Measure.Measure.comap_equivalence,
  Foundations.Measure.Measure.map_comap_equivalence,
  Foundations.Measure.Measure.IsFinite.comap,
  Foundations.Measure.Measure.SigmaFinite.comap,
  Foundations.Measure.Measure.SFinite.comap,
  Foundations.Measure.Measure.comap_probability_iff,
  Foundations.Measure.Measure.IsProbability.comap
]

#audit_registered_claims

#audit_package [Foundations.Measure.Additive.Comap] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
