import Foundations.Measure.Kernel.Rejection
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.retry,
  Foundations.Measure.Kernel.retry_apply,
  Foundations.Measure.Kernel.retry_mass,
  Foundations.Measure.Kernel.retry_comp_apply,
  Foundations.Measure.Kernel.retry_prefix_succ,
  Foundations.Measure.Kernel.retry_residual_succ,
  Foundations.Measure.Kernel.retry_residual_mass_succ,
  Foundations.Measure.Kernel.retry_conservative,
  Foundations.Measure.Kernel.retry_isFinite,
  Foundations.Measure.Kernel.loop_retry_reconstruct,
  Foundations.Measure.Kernel.retry_exit_normalizable,
  Foundations.Measure.Kernel.loop_retry_eq_normalize,
  Foundations.Measure.Kernel.loop_retry_isProbability,
  Foundations.Measure.Kernel.retry_vanishing_continuation,
  Foundations.Measure.Kernel.restriction_retry_conservative,
  Foundations.Measure.Kernel.loop_restriction_retry_eq_normalize,
  Foundations.Measure.Kernel.loop_restriction_retry_isProbability,
  Foundations.Measure.Kernel.Rejection.uniform_initial_retry,
  Foundations.Measure.Kernel.Rejection.uniform_initial_retry_isProbability,
  Foundations.Measure.Kernel.Rejection.Necessity.zero_acceptance
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Rejection] allowing [
  propext,
  Quot.sound,
  Classical.choice
]

#print axioms Foundations.Measure.Kernel.loop_retry_reconstruct
#print axioms Foundations.Measure.Kernel.loop_retry_eq_normalize
#print axioms Foundations.Measure.Kernel.loop_retry_isProbability
#print axioms Foundations.Measure.Kernel.retry_vanishing_continuation
#print axioms Foundations.Measure.Kernel.Rejection.uniform_initial_retry
#print axioms Foundations.Measure.Kernel.Rejection.Necessity.zero_acceptance
