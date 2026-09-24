import Problib.Real.Series
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.ENNReal.densityRatio,
  Problib.Real.ENNReal.densityRatio_mul_of_finite,
  Problib.Real.ENNReal.mul_densityRatio,
  Problib.Real.ENNReal.exists_sequence_supremum,
  Problib.Real.ENNReal.prefixMax,
  Problib.Real.ENNReal.prefixMax_step,
  Problib.Real.ENNReal.le_prefixMax,
  Problib.Real.ENNReal.prefixMax_le_iSup,
  Problib.Real.ENNReal.iSup_prefixMax,
  Problib.Real.ENNReal.tsum_sub_add,
  Problib.Real.ENNReal.tsum_sub,
  Problib.Real.ENNReal.partialSum_append,
  Problib.Real.ENNReal.partialSum_add_tail,
  Problib.Real.ENNReal.tail_le_tsum,
  Problib.Real.ENNReal.tail_antitone,
  Problib.Real.ENNReal.iInf_tail_eq_zero,
  Problib.Real.ENNReal.partialSum_step,
  Problib.Real.ENNReal.partialSum_monotone,
  Problib.Real.ENNReal.partialSum_le_tsum,
  Problib.Real.ENNReal.tsum_le,
  Problib.Real.ENNReal.tsum_least_upper_bound,
  Problib.Real.ENNReal.tsum_zero,
  Problib.Real.ENNReal.tsum_le_tsum,
  Problib.Real.ENNReal.tsum_single,
  Problib.Real.ENNReal.tsum_eq_zero_iff,
  Problib.Real.ENNReal.tsum_add,
  Problib.Real.ENNReal.tsum_mul_left,
  Problib.Real.ENNReal.tsum_const_of_ne_zero,
  Problib.Real.ENNReal.tsum_comm,
  Problib.Real.ENNReal.tsum_iSup,
  Problib.Real.ENNReal.tsum_reindex,
  Problib.Real.ENNReal.tsum_flatten,
  Problib.Real.ENNReal.exists_positive_summable_error,
  Problib.Real.ENNReal.rationalBasis_finite,
  Problib.Real.ENNReal.exists_rationalBasis,
  Problib.Real.ENNReal.exists_rationalBasis_between,
  Problib.Real.ENNReal.approximation_finite,
  Problib.Real.ENNReal.approximation_step,
  Problib.Real.ENNReal.approximation_le,
  Problib.Real.ENNReal.iSup_approximation
]

#audit_registered_claims

#audit_package [Problib.Real.Series] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
