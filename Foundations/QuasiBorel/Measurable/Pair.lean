module

public import Foundations.Measure.StandardBorel.Pair
public import Foundations.QuasiBorel.Measurable.Product

set_option autoImplicit false

namespace Foundations.QuasiBorel.Hom

open Foundations.Measure
open Foundations.Measure.Real (borel)

universe u

/-- Quasi-Borel morphism encoding pairs of reals into a single real coordinate. -/
@[expose] public noncomputable def realPairEncode {Ω : Type u}
    (source : Foundations.Measure.Space Ω) :
    Hom (Space.product (Space.ofMeasurable source borel) (Space.ofMeasurable source borel))
      (Space.ofMeasurable source borel) :=
  Hom.comp (Hom.ofMeasurable StandardBorel.RealPair.encode_measurable)
    (Space.productToMeasurable source borel borel)

/-- Quasi-Borel morphism decoding a single real coordinate into a pair of reals. -/
@[expose] public noncomputable def realPairDecode {Ω : Type u}
    (source : Foundations.Measure.Space Ω) :
    Hom (Space.ofMeasurable source borel)
      (Space.product (Space.ofMeasurable source borel) (Space.ofMeasurable source borel)) :=
  Hom.comp (Space.productOfMeasurable source borel borel)
    (Hom.ofMeasurable StandardBorel.RealPair.decode_measurable)

/-- The composite of real pair decode and encode morphisms is the identity morphism. -/
public theorem realPairDecode_realPairEncode {Ω : Type u} (source : Foundations.Measure.Space Ω) :
    Hom.comp (realPairDecode source) (realPairEncode source) =
      Hom.identity (Space.product (Space.ofMeasurable source borel) (Space.ofMeasurable source borel)) := by
  apply Hom.ext
  intro point
  exact StandardBorel.RealPair.decode_encode point

end Foundations.QuasiBorel.Hom
