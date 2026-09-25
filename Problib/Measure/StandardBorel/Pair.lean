module

public import Problib.Measure.StandardBorel.Product

set_option autoImplicit false

namespace Problib.Measure.StandardBorel

open Problib.Measure.Real (Carrier borel)

/-- Standard-Borel presentation of the product of two real Borel spaces. -/
@[expose] public noncomputable def realPair : StandardBorel (Space.product borel borel) :=
  real.product real

namespace RealPair

/-- Measurable embedding of pairs of reals into the real line. -/
@[expose] public noncomputable def encode : Carrier × Carrier → Carrier :=
  realPair.embeddingReal.function

/-- Measurable retraction decoding real numbers to pairs of reals with explicit origin fallback. -/
@[expose] public noncomputable def decode : Carrier → Carrier × Carrier :=
  realPair.embeddingReal.retract
    (Problib.Real.Construction.Dedekind.zero, Problib.Real.Construction.Dedekind.zero)

/-- Decoding an encoded pair of reals recovers the original pair. -/
public theorem decode_encode (point : Carrier × Carrier) : decode (encode point) = point :=
  realPair.embeddingReal.retract_forward _ point

/-- The pair encoding function into the real line is measurable. -/
public theorem encode_measurable : MeasurableMap (Space.product borel borel) borel encode :=
  realPair.embeddingReal.measurable

/-- The pair decoding retraction from the real line is measurable. -/
public theorem decode_measurable : MeasurableMap borel (Space.product borel borel) decode :=
  realPair.embeddingReal.retract_measurable _

/-- The pair encoding function into the real line is injective. -/
public theorem encode_injective : Function.Injective encode :=
  realPair.embeddingReal.injective

/-- The range of the pair encoding function is measurable in real Borel space. -/
public theorem range_measurable : borel.Measurable (Set.range encode) :=
  realPair.embeddingReal.range_measurable

end RealPair

end Problib.Measure.StandardBorel
