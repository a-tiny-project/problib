import Foundations.Measure.Coding
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Coding.Sequence.bits,
  Foundations.Measure.Coding.Sequence.bits_pair,
  Foundations.Measure.Coding.Sequence.encode,
  Foundations.Measure.Coding.Sequence.decode,
  Foundations.Measure.Coding.Sequence.decode_encode,
  Foundations.Measure.Coding.Sequence.bits_measurable,
  Foundations.Measure.Coding.Sequence.encode_measurable,
  Foundations.Measure.Coding.Sequence.decode_measurable,
  Foundations.Measure.Coding.term_measurable,
  Foundations.Measure.Coding.encode_measurable,
  Foundations.Measure.Coding.decodedPrefix_measurable,
  Foundations.Measure.Coding.digit_measurable,
  Foundations.Measure.Coding.Unit.bits,
  Foundations.Measure.Coding.Unit.selected,
  Foundations.Measure.Coding.Unit.value,
  Foundations.Measure.Coding.Unit.selected_bits_le,
  Foundations.Measure.Coding.Unit.value_bits,
  Foundations.Measure.Coding.Unit.bits_measurable,
  Foundations.Measure.Coding.Unit.value_measurable,
  Foundations.Measure.Coding.Pair.bits,
  Foundations.Measure.Coding.Pair.bits_even,
  Foundations.Measure.Coding.Pair.bits_odd,
  Foundations.Measure.Coding.Pair.encode,
  Foundations.Measure.Coding.Pair.decode,
  Foundations.Measure.Coding.Pair.decode_encode,
  Foundations.Measure.Coding.Pair.bits_measurable,
  Foundations.Measure.Coding.Pair.encode_measurable,
  Foundations.Measure.Coding.Pair.decode_measurable
]

#audit_registered_claims

#audit_package [Foundations.Measure.Coding] allowing [propext, Quot.sound, Classical.choice]
