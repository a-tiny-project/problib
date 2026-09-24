import Problib.Countable
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Countable.Pair.encode_decode,
  Problib.Countable.Pair.decode_encode,
  Problib.Countable.Pair.decode_bounds,
  Problib.Countable.Pair.decode_first_le,
  Problib.Countable.Pair.decode_second_le
]

#audit_registered_claims

#audit_package [Problib.Countable] allowing [propext, Quot.sound, Classical.choice]
