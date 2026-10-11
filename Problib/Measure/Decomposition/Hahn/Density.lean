module

public import Problib.Measure.Decomposition.Hahn.Basic
public import Problib.Measure.Decomposition.RadonNikodym.Basic
public import Problib.Measure.Integral.Density.Order

set_option autoImplicit false

/-!
# Hahn decomposition density bounds

Relates Hahn decomposition regions to Radon-Nikodym density inequalities almost
everywhere with respect to a finite reference measure.
-/

namespace Problib.Measure.Measure.HahnDecomposition

open Problib.Real

universe u

variable {α : Type u} {space : Space α} {left right reference : Measure space}

/-- On the positive region of a Hahn decomposition, the left measure's Radon-Nikodym
density dominates the right measure's density almost everywhere. -/
public theorem ae_density_le_on_region (decomposition : HahnDecomposition left right)
    (leftDerivative : RadonNikodymDerivative left reference)
    (rightDerivative : RadonNikodymDerivative right reference) (finite : IsFinite reference) :
    reference.AE (fun value => decomposition.region value →
      ENNReal.le (rightDerivative.density value) (leftDerivative.density value)) := by
  apply AE.of_restrict
  apply ae_le_of_withDensity_le_finite (finite.restrict decomposition.region)
    rightDerivative.density_measurable leftDerivative.density_measurable
  intro set measurable
  rw [reference.withDensity_restrict rightDerivative.density decomposition.measurable,
    reference.withDensity_restrict leftDerivative.density decomposition.measurable,
    ← rightDerivative.reconstruct_eq, ← leftDerivative.reconstruct_eq,
    right.restrict_apply decomposition.region measurable,
    left.restrict_apply decomposition.region measurable]
  exact decomposition.positive (space.inter measurable decomposition.measurable)
    (fun {_} member => member.2)

/-- Two-sided almost-everywhere bounds relating Hahn decomposition regions to density
order on both the positive region and its complement. -/
public theorem ae_density_bounds (decomposition : HahnDecomposition left right)
    (leftDerivative : RadonNikodymDerivative left reference)
    (rightDerivative : RadonNikodymDerivative right reference) (finite : IsFinite reference) :
    reference.AE (fun value =>
      (decomposition.region value → ENNReal.le (rightDerivative.density value) (leftDerivative.density value)) ∧
      (¬decomposition.region value → ENNReal.le (leftDerivative.density value) (rightDerivative.density value))) :=
  (decomposition.ae_density_le_on_region leftDerivative rightDerivative finite).and
    (decomposition.complement.ae_density_le_on_region rightDerivative leftDerivative finite)

end Problib.Measure.Measure.HahnDecomposition
