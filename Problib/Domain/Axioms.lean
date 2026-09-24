import Problib.Domain
import Problib.Domain.Necessity
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Domain.CPO.discrete,
  Problib.Domain.CPO.product,
  Problib.Domain.CPO.pi,
  Problib.Domain.CPO.powerset,
  Problib.Domain.CPO.continuous_from_discrete,
  Problib.Domain.CPO.continuous_sup,
  Problib.Domain.CPO.subtype,
  Problib.Domain.CPO.function,
  Problib.Domain.CPO.continuous_evaluate,
  Problib.Domain.CPO.continuous_curry,
  Problib.Domain.Pointed.powerset,
  Problib.Domain.Pointed.iterate_chain,
  Problib.Domain.Pointed.fix_unfold,
  Problib.Domain.Pointed.fix_least_prefixed,
  Problib.Domain.Pointed.fix_least,
  Problib.Domain.Pointed.fix_induction,
  Problib.Domain.Necessity.grow_continuous,
  Problib.Domain.Necessity.grow_fix_all,
  Problib.Domain.Necessity.bounded_bottom,
  Problib.Domain.Necessity.bounded_step,
  Problib.Domain.Necessity.admissibility_necessary,
  Problib.Domain.Necessity.bounded_not_admissible,
  Problib.Domain.Necessity.jump_monotone,
  Problib.Domain.Necessity.iterate_jump,
  Problib.Domain.Necessity.continuity_necessary,
  Problib.Domain.Necessity.jump_not_continuous,
  Problib.Domain.Necessity.pointedness_necessary,
  Problib.Domain.Necessity.monotonicity_necessary,
  Problib.Domain.Necessity.induction_base_necessary,
  Problib.Domain.Necessity.induction_step_necessary
]

#audit_registered_claims

#audit_package [Problib.Domain] allowing [propext, Quot.sound, Classical.choice]

#print axioms Problib.Domain.Pointed.fix_unfold
#print axioms Problib.Domain.Pointed.fix_least_prefixed
#print axioms Problib.Domain.Pointed.fix_induction
#print axioms Problib.Domain.CPO.continuous_sup
#print axioms Problib.Domain.CPO.continuous_evaluate
#print axioms Problib.Domain.CPO.continuous_curry
#print axioms Problib.Domain.Necessity.continuity_necessary
#print axioms Problib.Domain.Necessity.admissibility_necessary
