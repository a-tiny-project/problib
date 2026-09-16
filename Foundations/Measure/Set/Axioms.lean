import Foundations.Measure.Set.Family
import Foundations.Measure.Set.Image
import Foundations.Measure.Set.Difference
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Set.symmDiff,
  Foundations.Measure.Set.symmDiff_self,
  Foundations.Measure.Set.symmDiff_comm,
  Foundations.Measure.Set.symmDiff_complement,
  Foundations.Measure.Set.symmDiff_triangle,
  Foundations.Measure.Set.symmDiff_union,
  Foundations.Measure.Set.symmDiff_of_subset,
  Foundations.Measure.Set.subset_union_symmDiff,
  Foundations.Measure.Set.image,
  Foundations.Measure.Set.image_empty,
  Foundations.Measure.Set.image_univ,
  Foundations.Measure.Set.image_id,
  Foundations.Measure.Set.image_comp,
  Foundations.Measure.Set.image_mono,
  Foundations.Measure.Set.image_iUnion,
  Foundations.Measure.Set.image_pairwise,
  Foundations.Measure.Set.preimage_image,
  Foundations.Measure.Set.image_preimage,
  Foundations.Measure.Set.image_preimage_subset,
  Foundations.Measure.Set.image_inter_preimage,
  Foundations.Measure.Set.range_subtype,
  Foundations.Measure.Set.image_subtype_preimage,
  Foundations.Measure.Set.complement_complement,
  Foundations.Measure.Set.complement_union,
  Foundations.Measure.Set.complement_inter,
  Foundations.Measure.Set.complement_iUnion,
  Foundations.Measure.Set.complement_iInter,
  Foundations.Measure.Set.complement_difference,
  Foundations.Measure.Set.mem_prefixInter,
  Foundations.Measure.Set.prefixInter_antitone,
  Foundations.Measure.Set.iInter_prefixInter,
  Foundations.Measure.Set.ext,
  Foundations.Measure.Set.inter_iUnion,
  Foundations.Measure.Set.iUnion_inter,
  Foundations.Measure.Set.inter_difference_disjoint,
  Foundations.Measure.Set.inter_union_difference,
  Foundations.Measure.Set.preimage_iUnion,
  Foundations.Measure.Set.prefixUnion_monotone,
  Foundations.Measure.Set.iUnion_prefixUnion,
  Foundations.Measure.Set.prefixUnion_succ_eq_of_monotone,
  Foundations.Measure.Set.disjointed_subset,
  Foundations.Measure.Set.prefixUnion_disjoint_right,
  Foundations.Measure.Set.disjointed_pairwise,
  Foundations.Measure.Set.prefixUnion_disjointed,
  Foundations.Measure.Set.iUnion_disjointed
]

#audit_registered_claims

#audit_package [Foundations.Measure.Set] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
