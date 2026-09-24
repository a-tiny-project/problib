module

public import Problib.Measure.Coding.Pair
public import Problib.Measure.StandardBorel.Retraction

set_option autoImplicit false

namespace Problib.Measure.StandardBorel

universe u v

/-- Standard-Borel presentation of the unit square using real retraction coding. -/
@[expose] public noncomputable def unitSquare :
    StandardBorel (Space.product Problib.Measure.Real.unitBorel Problib.Measure.Real.unitBorel) :=
  ofRealLeftInverse Coding.Pair.encode Coding.Pair.decode Coding.Pair.decode_encode
    Coding.Pair.encode_measurable Coding.Pair.decode_measurable

/-- Standard-Borel presentation of the product of two standard-Borel spaces. -/
@[expose] public noncomputable def product {α : Type u} {β : Type v}
    {left : Space α} {right : Space β}
    (first : StandardBorel left) (second : StandardBorel right) :
    StandardBorel (Space.product left right) :=
  ofEmbedding (first.embedding.product second.embedding) unitSquare

end Problib.Measure.StandardBorel
