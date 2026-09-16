module

public import Foundations.QuasiBorel.SFinite.Product
public import Foundations.QuasiBorel.SFinite.Scale
public import Foundations.QuasiBorel.SFinite.Mass.Monad

/-!
# S-finite joint product marginals

This module identifies the marginal projections of independent joint products
in s-finite quasi-Borel spaces, proving that discarding one factor scales the
retained law by the discarded law's total mass. Normalized probability factors
preserve the opposite marginal for arbitrary retained laws.
-/

set_option autoImplicit false

namespace Foundations.QuasiBorel.SFinite

public section

open Foundations.Measure hiding Space
open Foundations.Real (ENNReal)

universe u v

variable {left : Space.{0, u} realSource} {right : Space.{0, v} realSource}

/-- Projecting the second marginal of a joint product scales the second law by the first law's mass. -/
theorem product_second (first : Law left) (second : Law right) :
    map (Space.second left right) (product left right (first, second)) =
      scale right (mass left first, second) := by
  rw [product_apply, map_bind]
  have equal : Hom.comp (map (Space.second left right))
      (Space.curry (Hom.comp (strength left right) (Space.swap (object right) left)) second) =
        Hom.constant left (object right) second := by
    apply Hom.ext
    intro point
    exact strength_second point second
  rw [equal, bind_const]

/-- Projecting the first marginal of a joint product scales the first law by the second law's mass. -/
theorem product_first (first : Law left) (second : Law right) :
    map (Space.first left right) (product left right (first, second)) =
      scale left (mass right second, first) := by
  rw [← product_second second first, ← product_swap first second]
  apply Law.ext
  rw [map_val, map_val, map_val, Measure.map_comp]
  rfl

/-- Total mass of a joint product law equals the product of factor masses. -/
theorem mass_product (first : Law left) (second : Law right) :
    mass (Space.product left right) (product left right (first, second)) =
      ENNReal.mul (mass left first) (mass right second) := by
  rw [← mass_map (Space.second left right), product_second, mass_scale]

/-- When the second law has mass one, projecting the first marginal recovers the first law. -/
theorem product_first_probability (first : Law left) (second : Law right)
    (normalized : Measure.IsProbability second.val) :
    map (Space.first left right) (product left right (first, second)) = first := by
  rw [product_first]
  change scale left (second.val Set.univ, first) = first
  rw [normalized.univ_eq_one, scale_one]

/-- When the first law has mass one, projecting the second marginal recovers the second law. -/
theorem product_second_probability (first : Law left) (second : Law right)
    (normalized : Measure.IsProbability first.val) :
    map (Space.second left right) (product left right (first, second)) = second := by
  rw [product_second]
  change scale right (first.val Set.univ, second) = second
  rw [normalized.univ_eq_one, scale_one]

end

end Foundations.QuasiBorel.SFinite
