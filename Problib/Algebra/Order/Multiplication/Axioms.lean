import Problib.Algebra.Order.Multiplication
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Algebra.OrderedCommutativeRingLaws.mul_zero,
  Problib.Algebra.OrderedCommutativeRingLaws.zero_mul,
  Problib.Algebra.OrderedCommutativeRingLaws.add_mul,
  Problib.Algebra.OrderedCommutativeRingLaws.neg_mul,
  Problib.Algebra.OrderedCommutativeRingLaws.mul_neg,
  Problib.Algebra.OrderedCommutativeRingLaws.neg_mul_neg,
  Problib.Algebra.OrderedCommutativeRingLaws.mul_le_mul_nonnegative_right,
  Problib.Algebra.OrderedCommutativeRingLaws.mul_le_mul_nonnegative_left,
  Problib.Algebra.NonnegativeMultiplicationKernel.signedMul_of_nonnegative_of_nonnegative,
  Problib.Algebra.NonnegativeMultiplicationKernel.signedMul_of_nonnegative_of_not_nonnegative,
  Problib.Algebra.NonnegativeMultiplicationKernel.signedMul_of_not_nonnegative_of_nonnegative,
  Problib.Algebra.NonnegativeMultiplicationKernel.signedMul_of_not_nonnegative_of_not_nonnegative
]

#audit_registered_claims

#audit_package [Problib.Algebra.Order.Multiplication] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
