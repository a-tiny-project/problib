import Foundations.Measure.StandardBorel.Real
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.StandardBorel.Real.encode,
  Foundations.Measure.StandardBorel.Real.decode,
  Foundations.Measure.StandardBorel.Real.encode_mem,
  Foundations.Measure.StandardBorel.Real.decode_encode,
  Foundations.Measure.StandardBorel.Real.encode_decode,
  Foundations.Measure.StandardBorel.Real.encode_monotone,
  Foundations.Measure.StandardBorel.Real.decode_monotone,
  Foundations.Measure.StandardBorel.real
]

#audit_registered_claims

#audit_package [Foundations.Measure.StandardBorel.Real] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
