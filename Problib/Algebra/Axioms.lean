import Problib.Algebra
import Problib.Algebra.Product
import Problib.Algebra.Sum
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
  Problib.Algebra.CommutativeSemiringLaws.add_mul,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_nil,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_cons,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_append,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_map_eq_foldr,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_perm,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_map_congr,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_map_eq_zero,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_map_zero,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_map_add,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_map_eq_single,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_comm,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_flatMap,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_hom,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_map_hom,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.finSum_zero,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.finSum_succ,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.finSum_eq_listSum,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.finSum_congr,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.finSum_const_zero,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.finSum_add,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.finSum_eq_single,
  Problib.Algebra.AdditiveCommutativeMonoidLaws.finSum_hom,
  Problib.Algebra.CommutativeSemiringLaws.listSum_map_mul_left,
  Problib.Algebra.CommutativeSemiringLaws.finSum_mul_left,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.listProduct_nil,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.listProduct_cons,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.listProduct_append,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.listProduct_perm,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.listProduct_map_mul,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.listProduct_map_eq_one,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.finProduct_zero,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.finProduct_succ,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.finProduct_eq_listProduct,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.finProduct_congr,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.finProduct_const_one,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.finProduct_mul,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.finProduct_eq_single,
  Problib.Algebra.MultiplicativeCommutativeMonoidLaws.finProduct_hom
]

#audit_registered_claims

#audit_package [Problib.Algebra] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
