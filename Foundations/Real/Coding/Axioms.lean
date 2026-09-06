import Foundations.Real.Coding
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.Coding.weight,
  Foundations.Real.Coding.term,
  Foundations.Real.Coding.term_le_weight,
  Foundations.Real.Coding.encode,
  Foundations.Real.Coding.encode_le_one,
  Foundations.Real.Coding.encode_finite,
  Foundations.Real.Coding.prefix_finite,
  Foundations.Real.Coding.threshold_iff,
  Foundations.Real.Coding.decodedPrefix,
  Foundations.Real.Coding.digit,
  Foundations.Real.Coding.prefix_encode,
  Foundations.Real.Coding.digit_encode,
  Foundations.Real.Coding.encode_injective
]

#audit_registered_claims

#audit_package [Foundations.Real.Coding] allowing [propext, Quot.sound, Classical.choice]
