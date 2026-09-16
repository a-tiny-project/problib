import Foundations.QuasiBorel.Domain
import Foundations.QuasiBorel.Domain.Example
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.QuasiBorel.Domain.Hom.identity_left,
  Foundations.QuasiBorel.Domain.Hom.identity_right,
  Foundations.QuasiBorel.Domain.Hom.comp_assoc,
  Foundations.QuasiBorel.Domain.Predomain.discrete,
  Foundations.QuasiBorel.Domain.Predomain.discrete_full,
  Foundations.QuasiBorel.Domain.Predomain.unrestricted,
  Foundations.QuasiBorel.Domain.Predomain.powerset,
  Foundations.QuasiBorel.Domain.Predomain.product,
  Foundations.QuasiBorel.Domain.Predomain.pi,
  Foundations.QuasiBorel.Domain.Predomain.first_pair,
  Foundations.QuasiBorel.Domain.Predomain.second_pair,
  Foundations.QuasiBorel.Domain.Predomain.pair_unique,
  Foundations.QuasiBorel.Domain.Predomain.terminate_unique,
  Foundations.QuasiBorel.Domain.Predomain.project_tuple,
  Foundations.QuasiBorel.Domain.Predomain.tuple_unique,
  Foundations.QuasiBorel.Domain.Predomain.homSup,
  Foundations.QuasiBorel.Domain.Predomain.homOrder,
  Foundations.QuasiBorel.Domain.Predomain.exponential,
  Foundations.QuasiBorel.Domain.Predomain.evaluate,
  Foundations.QuasiBorel.Domain.Predomain.curry,
  Foundations.QuasiBorel.Domain.Predomain.uncurry_curry,
  Foundations.QuasiBorel.Domain.Predomain.curry_uncurry,
  Foundations.QuasiBorel.Domain.Predomain.curry_unique,
  Foundations.QuasiBorel.Domain.Predomain.pointedProduct,
  Foundations.QuasiBorel.Domain.Predomain.pointedPi,
  Foundations.QuasiBorel.Domain.Predomain.pointedExponential,
  Foundations.QuasiBorel.Domain.Predomain.fix,
  Foundations.QuasiBorel.Domain.Predomain.fix_apply,
  Foundations.QuasiBorel.Domain.Predomain.fix_unfold,
  Foundations.QuasiBorel.Domain.Predomain.fix_least,
  Foundations.QuasiBorel.Domain.Predomain.fix_induction,
  Foundations.QuasiBorel.Domain.Example.powerset_pointed,
  Foundations.QuasiBorel.Domain.Example.powerset_nontrivial,
  Foundations.QuasiBorel.Domain.Example.grow_fix_all,
  Foundations.QuasiBorel.Domain.Example.grow_finite_approximants,
  Foundations.QuasiBorel.Domain.Example.grow_fix_not_finite_stage
]

#audit_registered_claims

#audit_package [Foundations.QuasiBorel.Domain] allowing [propext, Quot.sound, Classical.choice]

#print axioms Foundations.QuasiBorel.Domain.Predomain.exponential
#print axioms Foundations.QuasiBorel.Domain.Predomain.evaluate
#print axioms Foundations.QuasiBorel.Domain.Predomain.curry
#print axioms Foundations.QuasiBorel.Domain.Predomain.curry_uncurry
#print axioms Foundations.QuasiBorel.Domain.Predomain.fix
#print axioms Foundations.QuasiBorel.Domain.Predomain.fix_induction
#print axioms Foundations.QuasiBorel.Domain.Example.grow_fix_not_finite_stage
