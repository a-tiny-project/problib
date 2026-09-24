import Problib.Measure.StandardBorel.Real
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.StandardBorel.Real.encode,
  Problib.Measure.StandardBorel.Real.decode,
  Problib.Measure.StandardBorel.Real.encode_mem,
  Problib.Measure.StandardBorel.Real.decode_encode,
  Problib.Measure.StandardBorel.Real.encode_decode,
  Problib.Measure.StandardBorel.Real.encode_monotone,
  Problib.Measure.StandardBorel.Real.decode_monotone,
  Problib.Measure.StandardBorel.real
]

#audit_registered_claims

#audit_package [Problib.Measure.StandardBorel.Real] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
