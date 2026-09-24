import Problib.Measure.Coding
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Coding.Sequence.bits,
  Problib.Measure.Coding.Sequence.bits_pair,
  Problib.Measure.Coding.Sequence.encode,
  Problib.Measure.Coding.Sequence.decode,
  Problib.Measure.Coding.Sequence.decode_encode,
  Problib.Measure.Coding.Sequence.bits_measurable,
  Problib.Measure.Coding.Sequence.encode_measurable,
  Problib.Measure.Coding.Sequence.decode_measurable,
  Problib.Measure.Coding.term_measurable,
  Problib.Measure.Coding.encode_measurable,
  Problib.Measure.Coding.decodedPrefix_measurable,
  Problib.Measure.Coding.digit_measurable,
  Problib.Measure.Coding.Unit.bits,
  Problib.Measure.Coding.Unit.selected,
  Problib.Measure.Coding.Unit.value,
  Problib.Measure.Coding.Unit.selected_bits_le,
  Problib.Measure.Coding.Unit.value_bits,
  Problib.Measure.Coding.Unit.bits_measurable,
  Problib.Measure.Coding.Unit.value_measurable,
  Problib.Measure.Coding.Pair.bits,
  Problib.Measure.Coding.Pair.bits_even,
  Problib.Measure.Coding.Pair.bits_odd,
  Problib.Measure.Coding.Pair.encode,
  Problib.Measure.Coding.Pair.decode,
  Problib.Measure.Coding.Pair.decode_encode,
  Problib.Measure.Coding.Pair.bits_measurable,
  Problib.Measure.Coding.Pair.encode_measurable,
  Problib.Measure.Coding.Pair.decode_measurable
]

#audit_registered_claims

#audit_package [Problib.Measure.Coding] allowing [propext, Quot.sound, Classical.choice]
