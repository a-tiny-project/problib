import Problib.Measure.Kernel.Rejection
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.retry_residual,
  Problib.Measure.Kernel.boundedLoop_retry_exhausted,
  Problib.Measure.Kernel.retry_prefix_reconstruct,
  Problib.Measure.Kernel.retry_prefix_normalizable,
  Problib.Measure.Kernel.normalize_retry_prefix_eq_loop,
  Problib.Measure.Kernel.normalize_retry_prefix_eq_normalize_exit,
  Problib.Measure.Kernel.Rejection.Necessity.zero_budget,
  Problib.Measure.Kernel.Rejection.Necessity.zero_acceptance_bounded,
  Problib.Measure.Kernel.retry,
  Problib.Measure.Kernel.retry_apply,
  Problib.Measure.Kernel.retry_mass,
  Problib.Measure.Kernel.retry_comp_apply,
  Problib.Measure.Kernel.retry_prefix_succ,
  Problib.Measure.Kernel.retry_residual_succ,
  Problib.Measure.Kernel.retry_residual_mass_succ,
  Problib.Measure.Kernel.retry_conservative,
  Problib.Measure.Kernel.retry_isFinite,
  Problib.Measure.Kernel.loop_retry_reconstruct,
  Problib.Measure.Kernel.retry_exit_normalizable,
  Problib.Measure.Kernel.loop_retry_eq_normalize,
  Problib.Measure.Kernel.loop_retry_isProbability,
  Problib.Measure.Kernel.retry_vanishingContinuation,
  Problib.Measure.Kernel.restriction_retry_conservative,
  Problib.Measure.Kernel.loop_restriction_retry_eq_normalize,
  Problib.Measure.Kernel.loop_restriction_retry_isProbability,
  Problib.Measure.Kernel.Rejection.uniform_initial_retry,
  Problib.Measure.Kernel.Rejection.uniform_initial_retry_isProbability,
  Problib.Measure.Kernel.Rejection.Necessity.zero_acceptance
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Rejection] allowing [
  propext,
  Quot.sound,
  Classical.choice
]

#print axioms Problib.Measure.Kernel.loop_retry_reconstruct
#print axioms Problib.Measure.Kernel.loop_retry_eq_normalize
#print axioms Problib.Measure.Kernel.loop_retry_isProbability
#print axioms Problib.Measure.Kernel.retry_vanishingContinuation
#print axioms Problib.Measure.Kernel.Rejection.uniform_initial_retry
#print axioms Problib.Measure.Kernel.Rejection.Necessity.zero_acceptance
