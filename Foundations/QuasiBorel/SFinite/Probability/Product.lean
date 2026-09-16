import Foundations.QuasiBorel.SFinite.Probability.Closed
import Foundations.QuasiBorel.SFinite.Probability.Normalized
import Foundations.QuasiBorel.SFinite.Product

/-!
# Independent probability product expression under s-finite inclusion

This module proves that the independent probability product expression (constructed
from monadic bind and tensorial strength) commutes with the joint s-finite product
morphism, and that pairing probability laws yields a probability product law.
-/

set_option autoImplicit false

namespace Foundations.QuasiBorel.SFinite

open Foundations.Measure hiding Space

universe u v

variable {left : Space.{0, u} realSource} {right : Space.{0, v} realSource}

/-- Independent probability products expressed via bind and strength agree with s-finite products. -/
theorem ofProbability_product (first : Probability.Law left) (second : Probability.Law right) :
    ofProbability (Probability.bind first
      (Space.curry (Hom.comp (Probability.strength left right)
        (Space.swap (Probability.object right) left)) second)) =
      product left right (ofProbability first, ofProbability second) := by
  rw [ofProbability_bind, product_apply]
  apply congrArg (bind (ofProbability first))
  apply Hom.ext
  intro point
  exact ofProbability_strength point second

/-- The joint product of two probability laws is a probability law. -/
theorem product_probability (first : Law left) (second : Law right)
    (firstNormalized : Measure.IsProbability first.val)
    (secondNormalized : Measure.IsProbability second.val) :
    Measure.IsProbability (product left right (first, second)).val := by
  rcases (ofProbability_range first).mpr firstNormalized with ⟨first, rfl⟩
  rcases (ofProbability_range second).mpr secondNormalized with ⟨second, rfl⟩
  rw [← ofProbability_product]
  exact ofProbability_probability _

end Foundations.QuasiBorel.SFinite
