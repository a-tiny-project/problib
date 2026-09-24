import Problib.Probability.NNRat.Real
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Probability.NNRat.toENNReal,
  Problib.Probability.NNRat.toENNReal_zero,
  Problib.Probability.NNRat.toENNReal_one,
  Problib.Probability.NNRat.toENNReal_add,
  Problib.Probability.NNRat.toENNReal_mul,
  Problib.Probability.NNRat.toENNReal_injective,
  Problib.Probability.NNRat.toENNReal_eq_zero_iff,
  Problib.Probability.NNRat.toENNReal_finite
]

#audit_registered_claims

#audit_package [Problib.Probability.NNRat.Real] allowing [propext, Quot.sound, Classical.choice]
