module

public import Problib.Measure.Distribution.Uniqueness

set_option autoImplicit false

namespace Problib.Measure.Real.DistributionFunction

open Problib.Real
open Problib.Real.Construction

public section

/-- Distribution function for the Dirac point mass at zero: `F(x) = 1` for all `x ∈ [0, 1]`. -/
@[expose] noncomputable def atomZero : DistributionFunction where
  function := fun _ => unitOne
  monotone := fun _ => Dedekind.le_refl _
  upper := rfl
  right_continuous := by
    intro point room upper below
    rcases exists_unit_right_below point Dedekind.one room room with ⟨right, above, _⟩
    exact ⟨right, above, below⟩

theorem atomZero_measure_initial_zero : atomZero.measure (unitInitial unitZero) = ENNReal.one := by
  rw [atomZero.measure_initial]
  exact ENNReal.ofReal_toReal_finite NNReal.one

/-- The Dirac distribution assigns mass one to the origin singleton `{0}`. -/
theorem atomZero_singleton : atomZero.measure (Set.singleton unitZero) = ENNReal.one := by
  have same : Set.singleton unitZero = unitInitial unitZero := by
    apply Set.ext
    intro value
    constructor
    · intro member
      change value = unitZero at member
      rw [member]
      exact Dedekind.le_refl _
    · intro member
      exact Subtype.ext (Dedekind.le_antisymm member value.property.1)
  rw [same, atomZero_measure_initial_zero]

/-- Distribution function for the standard uniform distribution on `[0, 1]`: `F(x) = x`. -/
@[expose] noncomputable def identity : DistributionFunction where
  function := fun value => value
  monotone := fun included => included
  upper := rfl
  right_continuous := fun point room upper below => exists_unit_right_below point upper room below

theorem identity_quantile (threshold : UnitInterval) : identity.quantile threshold = threshold := by
  apply Subtype.ext
  exact Dedekind.le_antisymm
    ((identity.quantile_le_iff threshold threshold).mpr (Dedekind.le_refl _))
    (identity.quantile_member threshold)

/-- The measure induced by `identity` is exactly the standard uniform measure `uniform01`. -/
theorem identity_measure : identity.measure = uniform01 := by
  apply Eq.symm
  apply identity.measure_unique
  exact uniform01_unitInitial

/-- The measure induced by `atomZero` is exactly `dirac unitZero`. -/
theorem atomZero_measure : atomZero.measure = Measure.dirac unitBorel unitZero := by
  apply Eq.symm
  apply atomZero.measure_unique
  intro point
  rw [Measure.dirac_apply_of_mem unitBorel unitZero (unitInitial_measurable point)
    (show unitInitial point unitZero from point.property.1)]
  exact (ENNReal.ofReal_toReal_finite NNReal.one).symm

end

end Problib.Measure.Real.DistributionFunction
