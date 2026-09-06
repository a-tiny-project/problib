import Foundations.Algebra.Order.Multiplication
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Algebra.OrderedCommutativeRingLaws.mulZero,
  Foundations.Algebra.OrderedCommutativeRingLaws.zeroMul,
  Foundations.Algebra.OrderedCommutativeRingLaws.addMul,
  Foundations.Algebra.OrderedCommutativeRingLaws.negMul,
  Foundations.Algebra.OrderedCommutativeRingLaws.mulNeg,
  Foundations.Algebra.OrderedCommutativeRingLaws.negMulNeg,
  Foundations.Algebra.OrderedCommutativeRingLaws.mulLeMulNonnegativeRight,
  Foundations.Algebra.OrderedCommutativeRingLaws.mulLeMulNonnegativeLeft,
  Foundations.Algebra.NonnegativeMultiplicationKernel.signedMulOfNonnegativeOfNonnegative,
  Foundations.Algebra.NonnegativeMultiplicationKernel.signedMulOfNonnegativeOfNotNonnegative,
  Foundations.Algebra.NonnegativeMultiplicationKernel.signedMulOfNotNonnegativeOfNonnegative,
  Foundations.Algebra.NonnegativeMultiplicationKernel.signedMulOfNotNonnegativeOfNotNonnegative
]

#audit_registered_claims

#audit_package [Foundations.Algebra.Order.Multiplication] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
