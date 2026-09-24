module

public import Problib.QuasiBorel.SFinite.Product.Marginal

/-!
# Normalization necessity counterexample for s-finite quasi-Borel products

This module constructs an s-finite law with infinite total mass on the terminal space
and proves that projecting its product with a pure law does not recover the pure law.
This counterexample refutes unrestricted affine discard for general s-finite laws,
reusing the infinite score law on the terminal unit.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (borel)
open Problib.Real (ENNReal)

/-- Proves that an s-finite law with infinite total mass refutes affine projection discard. -/
theorem infinite_mass_product_not_affine :
    ∃ law : Law (Space.terminal realSource), law.val Set.univ = ENNReal.top ∧
      map (Space.second (Space.terminal realSource) (Space.terminal realSource))
        (product (Space.terminal realSource) (Space.terminal realSource)
          (law, pure (Space.terminal realSource) ())) ≠ pure (Space.terminal realSource) () := by
  let law := score ENNReal.top
  refine ⟨law, mass_score ENNReal.top, ?_⟩
  intro equal
  have total := congrArg (fun current : Law (Space.terminal realSource) => current.val Set.univ) equal
  rw [map_univ, product_pure_right, map_univ] at total
  change mass (Space.terminal realSource) (score ENNReal.top) =
    mass (Space.terminal realSource) (pure (Space.terminal realSource) ()) at total
  rw [mass_score, mass_pure] at total
  cases total

end

end Problib.QuasiBorel.SFinite
