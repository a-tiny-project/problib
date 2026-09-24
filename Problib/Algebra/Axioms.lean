import Problib.Algebra
import Problib.Algebra.Order.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Algebra.AdditiveCommutativeMonoidLaws.zero_add,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.add_left_comm,
  Problib.Algebra.AdditiveCommutativeGroupLaws.sub_eq_add_neg,
  Problib.Algebra.AdditiveCommutativeGroupLaws.zero_add,
  Problib.Algebra.AdditiveCommutativeGroupLaws.neg_add,
  Problib.Algebra.AdditiveCommutativeGroupLaws.add_neg_cancel_right,
  Problib.Algebra.AdditiveCommutativeGroupLaws.neg_add_cancel_left,
  Problib.Algebra.AdditiveCommutativeGroupLaws.add_left_cancel,
  Problib.Algebra.AdditiveCommutativeGroupLaws.add_right_cancel,
  Problib.Algebra.AdditiveCommutativeGroupLaws.add_left_comm,
  Problib.Algebra.AdditiveCommutativeGroupLaws.neg_neg,
  Problib.Algebra.AdditiveCommutativeGroupLaws.neg_zero,
  Problib.Algebra.AdditiveCommutativeGroupLaws.add_neg_eq_of_eq_add,
  Problib.Algebra.AdditiveCommutativeGroupLaws.eq_add_of_eq_neg_add,
  Problib.Algebra.AdditiveCommutativeGroupLaws.neg_add_distrib,
  Problib.Algebra.AdditiveCommutativeGroupLaws.neg_add_add_left,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.one_mul,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.mul_left_comm,
  Problib.Algebra.CommutativeSemiringLaws.mul_zero,
  Problib.Algebra.CommutativeSemiringLaws.add_mul
]

#audit_registered_claims

#audit_package [Problib.Algebra] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
