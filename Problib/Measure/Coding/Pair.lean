module

public import Problib.Measure.Coding.Stream
public import Problib.Measure.Coding.Unit
public import Problib.Measure.Product

set_option autoImplicit false

namespace Problib.Measure.Coding.Pair

open Problib.Real
open Problib.Measure.Real

/-- Interleave Boolean bits from two unit interval coordinates into a single stream. -/
@[expose] public noncomputable def bits (point : UnitInterval × UnitInterval) (index : Nat) : Bool :=
  if index % 2 = 0 then Unit.bits point.1 (index / 2) else Unit.bits point.2 (index / 2)

/-- Even bit positions extract the rational comparison bits of the first coordinate. -/
public theorem bits_even (point : UnitInterval × UnitInterval) (index : Nat) :
    bits point (2 * index) = Unit.bits point.1 index := by
  simp [bits, Nat.mul_comm]

/-- Odd bit positions extract the rational comparison bits of the second coordinate. -/
public theorem bits_odd (point : UnitInterval × UnitInterval) (index : Nat) :
    bits point (2 * index + 1) = Unit.bits point.2 index := by
  have remainder : (2 * index + 1) % 2 = 1 := by omega
  have quotient : (2 * index + 1) / 2 = index := by omega
  simp only [bits, remainder, quotient, Nat.one_ne_zero, if_false]

/-- Encode a pair of unit interval points into a real number. -/
@[expose] public noncomputable def encode (point : UnitInterval × UnitInterval) : Carrier :=
  ENNReal.toReal (Problib.Real.Coding.encode (bits point))

/-- Decode a real number into a pair of unit interval points. -/
@[expose] public noncomputable def decode (input : Carrier) : UnitInterval × UnitInterval :=
  (Unit.value (fun index => Problib.Real.Coding.digit (ENNReal.ofReal input) (2 * index)),
    Unit.value (fun index => Problib.Real.Coding.digit (ENNReal.ofReal input) (2 * index + 1)))

/-- Decoding an encoded pair of unit interval points recovers the original pair. -/
public theorem decode_encode (point : UnitInterval × UnitInterval) :
    decode (encode point) = point := by
  have represented : ENNReal.ofReal (encode point) = Problib.Real.Coding.encode (bits point) :=
    ENNReal.ofReal_toReal (Problib.Real.Coding.encode_finite (bits point))
  have even : (fun index => Problib.Real.Coding.digit (ENNReal.ofReal (encode point)) (2 * index)) =
      Unit.bits point.1 := by
    funext index
    rw [represented, Problib.Real.Coding.digit_encode, bits_even]
  have odd : (fun index => Problib.Real.Coding.digit (ENNReal.ofReal (encode point)) (2 * index + 1)) =
      Unit.bits point.2 := by
    funext index
    rw [represented, Problib.Real.Coding.digit_encode, bits_odd]
  unfold decode
  rw [even, odd, Unit.value_bits, Unit.value_bits]

/-- Each interleaved bit indicator event is measurable in the product unit Borel space. -/
public theorem bits_measurable (index : Nat) :
    (Space.product unitBorel unitBorel).Measurable (fun point => bits point index = true) := by
  by_cases even : index % 2 = 0
  · have equal : (fun point => bits point index = true) =
        Set.preimage Prod.fst (fun point => Unit.bits point (index / 2) = true) := by
      apply Set.ext
      intro point
      simp only [bits, if_pos even, Set.preimage]
    rw [equal]
    exact Space.first_measurable unitBorel unitBorel (Unit.bits_measurable (index / 2))
  · have equal : (fun point => bits point index = true) =
        Set.preimage Prod.snd (fun point => Unit.bits point (index / 2) = true) := by
      apply Set.ext
      intro point
      simp only [bits, if_neg even, Set.preimage]
    rw [equal]
    exact Space.second_measurable unitBorel unitBorel (Unit.bits_measurable (index / 2))

/-- Unit square encoding is a measurable map into real Borel space. -/
public theorem encode_measurable :
    MeasurableMap (Space.product unitBorel unitBorel) borel encode := by
  intro region measurable
  exact (Coding.encode_measurable bits_measurable).measurableMap (toReal_measurable measurable)

/-- Decoding real numbers into the unit square is a measurable map. -/
public theorem decode_measurable :
    MeasurableMap borel (Space.product unitBorel unitBorel) decode := by
  apply Space.pair_measurable
  · exact Unit.value_measurable (fun index =>
      ofReal_measurable.measurableMap (Coding.digit_measurable (2 * index)))
  · exact Unit.value_measurable (fun index =>
      ofReal_measurable.measurableMap (Coding.digit_measurable (2 * index + 1)))

end Problib.Measure.Coding.Pair
