import Foundations.Measure.Giry.Strength
import Foundations.QuasiBorel.Measurable.Pair
import Foundations.QuasiBorel.Probability.Monad

set_option autoImplicit false

namespace Foundations.QuasiBorel.Probability

open Foundations.Measure hiding Space
open Foundations.Measure.Real (Carrier borel)

universe u v w x

/-- Tensorial strength for the probability monad on quasi-Borel spaces, pairing a deterministic context value with a probability law. -/
noncomputable def strength (left right : Space (Source.ofMeasurable borel)) :
    Hom (Space.product left (object right)) (object (Space.product left right)) where
  toFun := fun point => map (Space.pairLeft left right point.1) point.2
  mapRandom := by
    intro random accepted
    let family := Classical.choice accepted.2
    refine ⟨{
      random := Space.pairRandom (fun seed => (random seed).1) family.random
      accepted := Space.pairRandom_accepted accepted.1 family.accepted
      kernel := fun seed => Giry.map StandardBorel.RealPair.encode StandardBorel.RealPair.encode_measurable
        (Giry.strength borel borel (seed, family.kernel seed))
      measurable := MeasurableMap.comp
        (Giry.map_measurable StandardBorel.RealPair.encode StandardBorel.RealPair.encode_measurable)
        (MeasurableMap.comp (Giry.strength_measurable borel borel)
          (Foundations.Measure.Space.pair_measurable (MeasurableMap.identity borel) family.measurable))
      law := ?_
    }⟩
    intro seed
    rw [map_val, ← family.law seed]
    unfold Giry.strength
    rw [Giry.map_comp, Giry.map_comp, Giry.map_comp]
    have equal :
        (fun point => Space.pairRandom (fun input => (random input).1) family.random
          (StandardBorel.RealPair.encode (seed, point))) =
        (fun point => ((random seed).1, family.random point)) :=
      funext (fun point => Space.pairRandom_encode _ _ (seed, point))
    simp only [equal]
    rfl
    exact Kernel.pair_left_measurable seed

variable {left right : Space (Source.ofMeasurable borel)}

/-- The underlying Giry law of a strengthened pair is the pushforward along the left pairing map. -/
theorem strength_val (point : left.Carrier) (law : Law right) :
    (strength left right (point, law)).val =
      Giry.map (Space.pairLeft left right point) (Space.pairLeft left right point).toMeasurable law.val :=
  map_val _ law

/-- Tensorial strength preserves monad unit (Dirac point mass). -/
theorem strength_pure (point : left.Carrier) (value : right.Carrier) :
    strength left right (point, pure right value) = pure (Space.product left right) (point, value) := by
  apply Law.ext
  rw [strength_val]
  exact Giry.map_pure (Space.pairLeft left right point) (Space.pairLeft left right point).toMeasurable value

/-- Naturality of tensorial strength with respect to morphisms on context and probability space. -/
theorem strength_natural {first second : Space (Source.ofMeasurable borel)}
    (firstMap : Hom left first) (secondMap : Hom right second)
    (point : left.Carrier) (law : Law right) :
    map (Space.productMap firstMap secondMap) (strength left right (point, law)) =
      strength first second (firstMap point, map secondMap law) := by
  apply Law.ext
  rw [map_val, strength_val, strength_val, map_val, Giry.map_comp, Giry.map_comp]
  rfl

/-- Projecting away the deterministic context from a strengthened pair recovers the original law. -/
theorem strength_second (point : left.Carrier) (law : Law right) :
    map (Space.second left right) (strength left right (point, law)) = law := by
  apply Law.ext
  rw [map_val, strength_val, Giry.map_comp]
  exact Giry.map_id law.val

/-- Tensorial strength with the terminal unit space recovers the law under canonical projection. -/
theorem strength_unit (law : Law right) :
    map (Space.second (Space.terminal (Source.ofMeasurable borel)) right)
      (strength (Space.terminal (Source.ofMeasurable borel)) right ((), law)) = law :=
  strength_second (left := Space.terminal (Source.ofMeasurable borel)) () law

/-- Associativity coherence for tensorial strength with respect to nested Cartesian products. -/
theorem strength_associate {third : Space (Source.ofMeasurable borel)}
    (first : left.Carrier) (second : right.Carrier) (law : Law third) :
    map (Space.associate left right third) (strength (Space.product left right) third ((first, second), law)) =
      strength left (Space.product right third) (first, strength right third (second, law)) := by
  apply Law.ext
  rw [map_val, strength_val, strength_val, strength_val, Giry.map_comp, Giry.map_comp]
  rfl

/-- Tensorial strength commutes with monadic bind. -/
theorem strength_bind {third : Space (Source.ofMeasurable borel)}
    (point : left.Carrier) (law : Law right) (kernel : Hom right (object third)) :
    strength left third (point, bind law kernel) =
      bind (strength left right (point, law))
        (Hom.comp (strength left third) (Space.productMap (Hom.identity left) kernel)) := by
  apply Law.ext
  rw [strength_val, bind_val, Giry.map_bind, bind_val, strength_val, Giry.bind_map]
  change _ = Giry.bind law.val (fun value => (strength left third (point, kernel value)).val) _
  simp only [strength_val]

end Foundations.QuasiBorel.Probability
