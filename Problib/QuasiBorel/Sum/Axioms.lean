import Problib.QuasiBorel.Sum.Laws
import Problib.QuasiBorel.Sum.Necessity
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.QuasiBorel.Space.initial,
  Problib.QuasiBorel.Space.initiate,
  Problib.QuasiBorel.Space.initiate_unique,
  Problib.QuasiBorel.Space.initial_no_random,
  Problib.QuasiBorel.SumRandom,
  Problib.QuasiBorel.Space.sum,
  Problib.QuasiBorel.Space.inl,
  Problib.QuasiBorel.Space.inr,
  Problib.QuasiBorel.Space.inl_apply,
  Problib.QuasiBorel.Space.inr_apply,
  Problib.QuasiBorel.Space.copair,
  Problib.QuasiBorel.Space.copair_inl,
  Problib.QuasiBorel.Space.copair_inr,
  Problib.QuasiBorel.Space.copair_unique,
  Problib.QuasiBorel.Space.sum_hom_ext,
  Problib.QuasiBorel.Space.sumMap,
  Problib.QuasiBorel.Space.sumMap_inl,
  Problib.QuasiBorel.Space.sumMap_inr,
  Problib.QuasiBorel.Space.sumMap_identity,
  Problib.QuasiBorel.Space.sumMap_comp,
  Problib.QuasiBorel.Space.sumSwap,
  Problib.QuasiBorel.Space.sumSwap_involutive,
  Problib.QuasiBorel.Space.sumAssociate,
  Problib.QuasiBorel.Space.sumUnassociate,
  Problib.QuasiBorel.Space.sumAssociate_sumUnassociate,
  Problib.QuasiBorel.Space.sumUnassociate_sumAssociate,
  Problib.QuasiBorel.Space.sumInitialLeft,
  Problib.QuasiBorel.Space.sumInitialRight,
  Problib.QuasiBorel.Space.sumInitialLeft_inr,
  Problib.QuasiBorel.Space.inr_sumInitialLeft,
  Problib.QuasiBorel.Space.sumInitialRight_inl,
  Problib.QuasiBorel.Space.inl_sumInitialRight,
  Problib.QuasiBorel.Sum.Necessity.total_branches_exclude_empty_summand,
  Problib.QuasiBorel.Sum.Necessity.initial_left_accepts_right_constant,
  Problib.QuasiBorel.Sum.Necessity.initial_right_accepts_left_constant,
  Problib.QuasiBorel.Sum.Necessity.unrestricted_empty_is_not_initial
]

#audit_registered_claims

#audit_package [Problib.QuasiBorel.Sum] allowing [propext, Quot.sound, Classical.choice]
