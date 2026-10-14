import Problib.Algebra.Order.Nonnegative
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Algebra.NonnegativePart.ext,
  Problib.Algebra.NonnegativePart.add_comm,
  Problib.Algebra.NonnegativePart.add_assoc,
  Problib.Algebra.NonnegativePart.add_zero,
  Problib.Algebra.NonnegativePart.add_left_cancel,
  Problib.Algebra.NonnegativeMultiplicationKernel.mul_zero,
  Problib.Algebra.NonnegativeMultiplicationKernel.zero_mul
]

#audit_registered_claims

#audit_package [Problib.Algebra.Order.Nonnegative] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
