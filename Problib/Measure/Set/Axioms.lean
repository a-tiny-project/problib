import Problib.Measure.Set.Family
import Problib.Measure.Set.Image
import Problib.Measure.Set.Difference
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Set.symmDiff,
  Problib.Measure.Set.symmDiff_self,
  Problib.Measure.Set.symmDiff_comm,
  Problib.Measure.Set.symmDiff_complement,
  Problib.Measure.Set.symmDiff_triangle,
  Problib.Measure.Set.symmDiff_union,
  Problib.Measure.Set.symmDiff_of_subset,
  Problib.Measure.Set.subset_union_symmDiff,
  Problib.Measure.Set.image,
  Problib.Measure.Set.image_empty,
  Problib.Measure.Set.image_univ,
  Problib.Measure.Set.image_id,
  Problib.Measure.Set.image_comp,
  Problib.Measure.Set.image_mono,
  Problib.Measure.Set.image_iUnion,
  Problib.Measure.Set.image_pairwise,
  Problib.Measure.Set.preimage_image,
  Problib.Measure.Set.image_preimage,
  Problib.Measure.Set.image_preimage_subset,
  Problib.Measure.Set.image_inter_preimage,
  Problib.Measure.Set.range_subtype,
  Problib.Measure.Set.image_subtype_preimage,
  Problib.Measure.Set.complement_complement,
  Problib.Measure.Set.complement_union,
  Problib.Measure.Set.complement_inter,
  Problib.Measure.Set.complement_iUnion,
  Problib.Measure.Set.complement_iInter,
  Problib.Measure.Set.complement_difference,
  Problib.Measure.Set.mem_prefixInter,
  Problib.Measure.Set.prefixInter_antitone,
  Problib.Measure.Set.iInter_prefixInter,
  Problib.Measure.Set.ext,
  Problib.Measure.Set.inter_iUnion,
  Problib.Measure.Set.iUnion_inter,
  Problib.Measure.Set.inter_difference_disjoint,
  Problib.Measure.Set.inter_union_difference,
  Problib.Measure.Set.preimage_iUnion,
  Problib.Measure.Set.prefixUnion_monotone,
  Problib.Measure.Set.iUnion_prefixUnion,
  Problib.Measure.Set.prefixUnion_succ_eq_of_monotone,
  Problib.Measure.Set.disjointed_subset,
  Problib.Measure.Set.prefixUnion_disjoint_right,
  Problib.Measure.Set.disjointed_pairwise,
  Problib.Measure.Set.prefixUnion_disjointed,
  Problib.Measure.Set.iUnion_disjointed
]

#audit_registered_claims

#audit_package [Problib.Measure.Set] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
