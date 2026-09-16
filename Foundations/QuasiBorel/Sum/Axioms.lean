import Foundations.QuasiBorel.Sum.Laws
import Foundations.QuasiBorel.Sum.Necessity
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.QuasiBorel.Space.initial,
  Foundations.QuasiBorel.Space.initiate,
  Foundations.QuasiBorel.Space.initiate_unique,
  Foundations.QuasiBorel.Space.initial_no_random,
  Foundations.QuasiBorel.SumRandom,
  Foundations.QuasiBorel.Space.sum,
  Foundations.QuasiBorel.Space.inl,
  Foundations.QuasiBorel.Space.inr,
  Foundations.QuasiBorel.Space.inl_apply,
  Foundations.QuasiBorel.Space.inr_apply,
  Foundations.QuasiBorel.Space.copair,
  Foundations.QuasiBorel.Space.copair_inl,
  Foundations.QuasiBorel.Space.copair_inr,
  Foundations.QuasiBorel.Space.copair_unique,
  Foundations.QuasiBorel.Space.sum_hom_ext,
  Foundations.QuasiBorel.Space.sumMap,
  Foundations.QuasiBorel.Space.sumMap_inl,
  Foundations.QuasiBorel.Space.sumMap_inr,
  Foundations.QuasiBorel.Space.sumMap_identity,
  Foundations.QuasiBorel.Space.sumMap_comp,
  Foundations.QuasiBorel.Space.sumSwap,
  Foundations.QuasiBorel.Space.sumSwap_involutive,
  Foundations.QuasiBorel.Space.sumAssociate,
  Foundations.QuasiBorel.Space.sumUnassociate,
  Foundations.QuasiBorel.Space.sumAssociate_sumUnassociate,
  Foundations.QuasiBorel.Space.sumUnassociate_sumAssociate,
  Foundations.QuasiBorel.Space.sumInitialLeft,
  Foundations.QuasiBorel.Space.sumInitialRight,
  Foundations.QuasiBorel.Space.sumInitialLeft_inr,
  Foundations.QuasiBorel.Space.inr_sumInitialLeft,
  Foundations.QuasiBorel.Space.sumInitialRight_inl,
  Foundations.QuasiBorel.Space.inl_sumInitialRight,
  Foundations.QuasiBorel.Sum.Necessity.total_branches_exclude_empty_summand,
  Foundations.QuasiBorel.Sum.Necessity.initial_left_accepts_right_constant,
  Foundations.QuasiBorel.Sum.Necessity.initial_right_accepts_left_constant,
  Foundations.QuasiBorel.Sum.Necessity.unrestricted_empty_is_not_initial
]

#audit_registered_claims

#audit_package [Foundations.QuasiBorel.Sum] allowing [propext, Quot.sound, Classical.choice]
