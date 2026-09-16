import Foundations.QuasiBorel.SFinite.Probability.Monad
import Foundations.QuasiBorel.SFinite.Strength
import Foundations.QuasiBorel.Probability.Strength

/-!
# Tensorial strength preservation under s-finite inclusion

This module proves that the canonical inclusion of probability laws into s-finite
laws preserves tensorial strength, commuting with pairing and product morphisms.
-/

set_option autoImplicit false

namespace Foundations.QuasiBorel.SFinite

universe u v

variable {left : Space.{0, u} realSource} {right : Space.{0, v} realSource}

/-- Tensorial strength on probability laws commutes with inclusion into s-finite laws. -/
theorem ofProbability_strength (point : left.Carrier) (law : Probability.Law right) :
    ofProbability (Probability.strength left right (point, law)) =
      strength left right (point, ofProbability law) := by
  apply Law.ext
  rw [ofProbability_val, strength_val, ofProbability_val, Probability.strength_val]
  rfl

/-- Tensorial strength morphism on probability laws commutes with s-finite strength. -/
theorem ofProbability_strength_hom (left : Space.{0, u} realSource)
    (right : Space.{0, v} realSource) :
    Hom.comp (ofProbabilityHom (Space.product left right)) (Probability.strength left right) =
      Hom.comp (strength left right) (Space.productMap (Hom.identity left) (ofProbabilityHom right)) := by
  apply Hom.ext
  intro point
  exact ofProbability_strength point.1 point.2

end Foundations.QuasiBorel.SFinite
