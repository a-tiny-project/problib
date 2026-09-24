import Problib.QuasiBorel.Domain
import Problib.QuasiBorel.Domain.Example
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.QuasiBorel.Domain.Hom.identity_left,
  Problib.QuasiBorel.Domain.Hom.identity_right,
  Problib.QuasiBorel.Domain.Hom.comp_assoc,
  Problib.QuasiBorel.Domain.Predomain.discrete,
  Problib.QuasiBorel.Domain.Predomain.discrete_full,
  Problib.QuasiBorel.Domain.Predomain.unrestricted,
  Problib.QuasiBorel.Domain.Predomain.powerset,
  Problib.QuasiBorel.Domain.Predomain.product,
  Problib.QuasiBorel.Domain.Predomain.pi,
  Problib.QuasiBorel.Domain.Predomain.first_pair,
  Problib.QuasiBorel.Domain.Predomain.second_pair,
  Problib.QuasiBorel.Domain.Predomain.pair_unique,
  Problib.QuasiBorel.Domain.Predomain.terminate_unique,
  Problib.QuasiBorel.Domain.Predomain.project_tuple,
  Problib.QuasiBorel.Domain.Predomain.tuple_unique,
  Problib.QuasiBorel.Domain.Predomain.homSup,
  Problib.QuasiBorel.Domain.Predomain.homOrder,
  Problib.QuasiBorel.Domain.Predomain.exponential,
  Problib.QuasiBorel.Domain.Predomain.evaluate,
  Problib.QuasiBorel.Domain.Predomain.curry,
  Problib.QuasiBorel.Domain.Predomain.uncurry_curry,
  Problib.QuasiBorel.Domain.Predomain.curry_uncurry,
  Problib.QuasiBorel.Domain.Predomain.curry_unique,
  Problib.QuasiBorel.Domain.Predomain.pointedProduct,
  Problib.QuasiBorel.Domain.Predomain.pointedPi,
  Problib.QuasiBorel.Domain.Predomain.pointedExponential,
  Problib.QuasiBorel.Domain.Predomain.fix,
  Problib.QuasiBorel.Domain.Predomain.fix_apply,
  Problib.QuasiBorel.Domain.Predomain.fix_unfold,
  Problib.QuasiBorel.Domain.Predomain.fix_least,
  Problib.QuasiBorel.Domain.Predomain.fix_induction,
  Problib.QuasiBorel.Domain.Example.powerset_pointed,
  Problib.QuasiBorel.Domain.Example.powerset_nontrivial,
  Problib.QuasiBorel.Domain.Example.grow_fix_all,
  Problib.QuasiBorel.Domain.Example.grow_finite_approximants,
  Problib.QuasiBorel.Domain.Example.grow_fix_not_finite_stage
]

#audit_registered_claims

#audit_package [Problib.QuasiBorel.Domain] allowing [propext, Quot.sound, Classical.choice]

#print axioms Problib.QuasiBorel.Domain.Predomain.exponential
#print axioms Problib.QuasiBorel.Domain.Predomain.evaluate
#print axioms Problib.QuasiBorel.Domain.Predomain.curry
#print axioms Problib.QuasiBorel.Domain.Predomain.curry_uncurry
#print axioms Problib.QuasiBorel.Domain.Predomain.fix
#print axioms Problib.QuasiBorel.Domain.Predomain.fix_induction
#print axioms Problib.QuasiBorel.Domain.Example.grow_fix_not_finite_stage
