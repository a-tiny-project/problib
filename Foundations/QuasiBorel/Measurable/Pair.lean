module

public import Foundations.Measure.StandardBorel.Pair
public import Foundations.QuasiBorel.Measurable.Product
public import Foundations.QuasiBorel.Measurable.Induced

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

namespace Foundations.QuasiBorel.Space

open Foundations.Measure hiding Space
open Foundations.Measure.Real (Carrier borel)

universe v w

/-- Pairs two maps from the real random source into a product map by decoding a single real seed into real coordinates. -/
@[expose] public noncomputable def pairRandom {α : Type v} {β : Type w}
    (first : Foundations.Measure.Real.Carrier → α) (second : Foundations.Measure.Real.Carrier → β)
    (seed : Foundations.Measure.Real.Carrier) : α × β :=
  (first (StandardBorel.RealPair.decode seed).1, second (StandardBorel.RealPair.decode seed).2)

/-- Evaluating the paired random map on an encoded real coordinate pair recovers the separate evaluations. -/
public theorem pairRandom_encode {α : Type v} {β : Type w}
    (first : Foundations.Measure.Real.Carrier → α) (second : Foundations.Measure.Real.Carrier → β)
    (point : Foundations.Measure.Real.Carrier × Foundations.Measure.Real.Carrier) :
    pairRandom first second (StandardBorel.RealPair.encode point) = (first point.1, second point.2) := by
  unfold pairRandom
  rw [StandardBorel.RealPair.decode_encode]

/-- Pairing two accepted random elements yields an accepted random element into the Cartesian product space. -/
public theorem pairRandom_accepted {left right : Space (Source.ofMeasurable borel)}
    {first : Foundations.Measure.Real.Carrier → left.Carrier}
    {second : Foundations.Measure.Real.Carrier → right.Carrier}
    (firstAccepted : left.Random first) (secondAccepted : right.Random second) :
    (product left right).Random (pairRandom first second) :=
  ⟨left.reparam (MeasurableMap.comp (Foundations.Measure.Space.first_measurable borel borel)
      StandardBorel.RealPair.decode_measurable) firstAccepted,
    right.reparam (MeasurableMap.comp (Foundations.Measure.Space.second_measurable borel borel)
      StandardBorel.RealPair.decode_measurable) secondAccepted⟩

/-- The product of two accepted random elements is measurable from the product Borel space into the sigma-algebra induced by the quasi-Borel product. -/
public theorem random_pair_measurable {left right : Space (Source.ofMeasurable borel)}
    {first : Foundations.Measure.Real.Carrier → left.Carrier}
    {second : Foundations.Measure.Real.Carrier → right.Carrier}
    (firstAccepted : left.Random first) (secondAccepted : right.Random second) :
    MeasurableMap (Foundations.Measure.Space.product borel borel) (product left right).toMeasurable
      (fun point => (first point.1, second point.2)) := by
  have equal : (fun point => pairRandom first second (StandardBorel.RealPair.encode point)) =
      (fun point => (first point.1, second point.2)) := funext (pairRandom_encode first second)
  rw [← equal]
  intro region measurable
  exact StandardBorel.RealPair.encode_measurable
    (random_measurable (pairRandom_accepted firstAccepted secondAccepted) measurable)

end Foundations.QuasiBorel.Space
