import Problib.Real.Coding
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.Coding.weight,
  Problib.Real.Coding.term,
  Problib.Real.Coding.term_le_weight,
  Problib.Real.Coding.encode,
  Problib.Real.Coding.encode_le_one,
  Problib.Real.Coding.encode_finite,
  Problib.Real.Coding.prefix_finite,
  Problib.Real.Coding.threshold_iff,
  Problib.Real.Coding.decodedPrefix,
  Problib.Real.Coding.digit,
  Problib.Real.Coding.prefix_encode,
  Problib.Real.Coding.digit_encode,
  Problib.Real.Coding.encode_injective
]

#audit_registered_claims

#audit_package [Problib.Real.Coding] allowing [propext, Quot.sound, Classical.choice]
