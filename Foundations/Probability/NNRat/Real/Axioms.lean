import Foundations.Probability.NNRat.Real
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Probability.NNRat.toENNReal,
  Foundations.Probability.NNRat.toENNReal_zero,
  Foundations.Probability.NNRat.toENNReal_one,
  Foundations.Probability.NNRat.toENNReal_add,
  Foundations.Probability.NNRat.toENNReal_mul,
  Foundations.Probability.NNRat.toENNReal_injective,
  Foundations.Probability.NNRat.toENNReal_eq_zero_iff,
  Foundations.Probability.NNRat.toENNReal_finite
]

#audit_registered_claims

#audit_package [Foundations.Probability.NNRat.Real] allowing [propext, Quot.sound, Classical.choice]
