import Problib.Algebra.Order
import Problib.Algebra.Order.Multiplication.Axioms
import Problib.Algebra.Order.Nonnegative.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.add_le_add_right,
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.le_of_add_le_add_right,
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.add_le_add_right_iff,
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.add_le_add_left,
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.le_of_add_le_add_left,
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.add_le_add_left_iff,
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.add_le_add,
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.neg_antitone,
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.neg_le_neg_iff,
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.sub_nonnegative_of_le,
  Problib.Algebra.OrderedAdditiveCommutativeGroupLaws.le_of_sub_nonnegative,
  Problib.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.nonpositive_of_not_nonnegative,
  Problib.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.neg_nonnegative_of_nonpositive,
  Problib.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.neg_nonpositive_of_nonnegative,
  Problib.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.neg_nonnegative_of_not_nonnegative,
  Problib.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.nonpositive_of_neg_nonnegative,
  Problib.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.eq_zero_of_nonnegative_of_neg_nonnegative
]

#audit_registered_claims

#audit_package [Problib.Algebra.Order] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
