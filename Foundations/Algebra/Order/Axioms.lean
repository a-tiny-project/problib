import Foundations.Algebra.Order
import Foundations.Algebra.Order.Multiplication.Axioms
import Foundations.Algebra.Order.Nonnegative.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.addLeAddRight,
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.leOfAddLeAddRight,
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.addLeAddRightIff,
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.addLeAddLeft,
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.leOfAddLeAddLeft,
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.addLeAddLeftIff,
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.addLeAdd,
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.negAntitone,
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.negLeNegIff,
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.subNonnegativeOfLe,
  Foundations.Algebra.OrderedAdditiveCommutativeGroupLaws.leOfSubNonnegative,
  Foundations.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.nonpositiveOfNotNonnegative,
  Foundations.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.negNonnegativeOfNonpositive,
  Foundations.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.negNonpositiveOfNonnegative,
  Foundations.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.negNonnegativeOfNotNonnegative,
  Foundations.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.nonpositiveOfNegNonnegative,
  Foundations.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws.eqZeroOfNonnegativeOfNegNonnegative
]

#audit_registered_claims

#audit_package [Foundations.Algebra.Order] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
