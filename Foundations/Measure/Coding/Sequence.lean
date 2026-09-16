module

public import Foundations.Measure.Coding.Stream
public import Foundations.Measure.Coding.Unit
public import Foundations.Measure.Pi
public import Foundations.Countable.Bijection

set_option autoImplicit false

namespace Foundations.Measure.Coding.Sequence

open Foundations.Real
open Foundations.Measure.Real

public section

/-- Interleaved rational-threshold comparison bits encoding a sequence of
unit-interval points into a single Boolean stream. -/
@[expose] noncomputable def bits (point : Nat → UnitInterval) (index : Nat) : Bool :=
  Unit.bits (point (Countable.Pair.decode index).1) (Countable.Pair.decode index).2

/-- Evaluating sequence bits at an encoded pair recovers the coordinate point
comparison bit. -/
theorem bits_pair (point : Nat → UnitInterval) (coordinate index : Nat) :
    bits point (Countable.Pair.encode (coordinate, index)) = Unit.bits (point coordinate) index := by
  simp only [bits, Countable.Pair.decodeEncode]

/-- Measurable real encoding of a sequence of unit-interval points through
separated-digit stream coding. -/
@[expose] noncomputable def encode (point : Nat → UnitInterval) : Carrier :=
  ENNReal.toReal (Foundations.Real.Coding.encode (bits point))

/-- Measurable decoding of a real number into a sequence of unit-interval points. -/
@[expose] noncomputable def decode (input : Carrier) : Nat → UnitInterval :=
  fun coordinate => Unit.value (fun index =>
    Foundations.Real.Coding.digit (ENNReal.ofReal input) (Countable.Pair.encode (coordinate, index)))

/-- Left inverse recovery: decoding an encoded sequence recovers the original
sequence. -/
theorem decode_encode (point : Nat → UnitInterval) : decode (encode point) = point := by
  have represented : ENNReal.ofReal (encode point) = Foundations.Real.Coding.encode (bits point) :=
    ENNReal.ofRealToReal (Foundations.Real.Coding.encode_finite (bits point))
  funext coordinate
  have digits : (fun index => Foundations.Real.Coding.digit (ENNReal.ofReal (encode point))
      (Countable.Pair.encode (coordinate, index))) = Unit.bits (point coordinate) := by
    funext index
    rw [represented, Foundations.Real.Coding.digit_encode, bits_pair]
  change Unit.value _ = point coordinate
  rw [digits, Unit.value_bits]

/-- Each interleaved comparison bit predicate is measurable in the product space. -/
theorem bits_measurable (index : Nat) :
    (Space.pi (fun _ : Nat => unitBorel)).Measurable (fun point => bits point index = true) :=
  Space.coordinate_measurable (fun _ : Nat => unitBorel) (Countable.Pair.decode index).1
    (Unit.bits_measurable (Countable.Pair.decode index).2)

/-- The sequence encoder is measurable from the product space to the real
Borel space. -/
theorem encode_measurable :
    MeasurableMap (Space.pi (fun _ : Nat => unitBorel)) borel encode := by
  intro region measurable
  exact (Coding.encode_measurable bits_measurable).measurableMap (toRealMeasurable measurable)

/-- The sequence decoder is measurable from the real Borel space to the
product space. -/
theorem decode_measurable :
    MeasurableMap borel (Space.pi (fun _ : Nat => unitBorel)) decode :=
  Space.pi_measurable (fun coordinate => Unit.value_measurable (fun index =>
    ofRealMeasurable.measurableMap (Coding.digit_measurable (Countable.Pair.encode (coordinate, index)))))

end

end Foundations.Measure.Coding.Sequence
