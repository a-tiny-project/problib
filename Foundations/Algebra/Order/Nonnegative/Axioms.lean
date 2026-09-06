import Foundations.Algebra.Order.Nonnegative
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Algebra.NonnegativePart.ext,
  Foundations.Algebra.NonnegativePart.addComm,
  Foundations.Algebra.NonnegativePart.addAssoc,
  Foundations.Algebra.NonnegativePart.addZero,
  Foundations.Algebra.NonnegativePart.addLeftCancel,
  Foundations.Algebra.NonnegativeMultiplicationKernel.mulZero,
  Foundations.Algebra.NonnegativeMultiplicationKernel.zeroMul
]

#audit_registered_claims

#audit_package [Foundations.Algebra.Order.Nonnegative] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
