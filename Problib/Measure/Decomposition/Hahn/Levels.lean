module

public import Problib.Measure.Extended.Limit
public import Problib.Measure.AlmostEverywhere.Basic
public import Problib.Real.Series.Basis

set_option autoImplicit false

/-!
# Rational Hahn level density construction

Constructs a nonnegative measurable density from a sequence of rational Hahn
level sets. Proves almost-everywhere equality with any density satisfying the
level bounds.
-/

namespace Problib.Measure.Measure.Hahn

open Problib.Real

universe u

variable {α : Type u} {space : Space α}

/-- Density constructed as the supremum of rational basis values over their indicator level sets. -/
@[expose] public noncomputable def levelDensity (regions : Nat → Set α) : α → ENNReal :=
  fun value => ENNReal.iSup (fun index =>
    ennrealIndicator (regions index) (fun _ => ENNReal.rationalBasis index) value)

/-- Measurability of the rational Hahn level density from measurable level sets. -/
public theorem levelDensity_measurable (regions : Nat → Set α)
    (measurable : ∀ index, space.Measurable (regions index)) :
    ENNRealMeasurable space (levelDensity regions) :=
  ENNRealMeasurable.iSup (fun index =>
    ENNRealMeasurable.indicator (measurable index) (ENNRealMeasurable.constant space _))

/-- Almost-everywhere equality of the reconstructed level density with any density satisfying
the two-sided level bounds. -/
public theorem ae_levelDensity_eq (measure : Measure space) (regions : Nat → Set α)
    (density : α → ENNReal)
    (bounds : ∀ index, measure.AE (fun value =>
      (regions index value → ENNReal.le (ENNReal.rationalBasis index) (density value)) ∧
      (¬regions index value → ENNReal.le (density value) (ENNReal.rationalBasis index)))) :
    measure.AEEq (levelDensity regions) density := by
  classical
  apply (ae_all_iff.mpr bounds).mono
  intro value bounded
  have upper : ENNReal.le (levelDensity regions value) (density value) := by
    apply ENNReal.iSup_le
    intro index
    by_cases member : regions index value
    · simpa only [ennrealIndicator, ennrealPiecewise, if_pos member] using (bounded index).1 member
    · simpa only [ennrealIndicator, ennrealPiecewise, if_neg member] using ENNReal.zero_le (density value)
  apply ENNReal.le_antisymm upper
  apply Classical.byContradiction
  intro notIncluded
  rcases ENNReal.exists_rationalBasis_between ⟨upper, notIncluded⟩ with ⟨index, above, below⟩
  have member : regions index value := by
    apply Classical.byContradiction
    intro absent
    exact below.2 ((bounded index).2 absent)
  have lower := ENNReal.le_iSup (fun index =>
    ennrealIndicator (regions index) (fun _ => ENNReal.rationalBasis index) value) index
  have term : ennrealIndicator (regions index) (fun _ => ENNReal.rationalBasis index) value =
      ENNReal.rationalBasis index := by
    simp only [ennrealIndicator, ennrealPiecewise, if_pos member]
  rw [term] at lower
  exact above.2 lower

end Problib.Measure.Measure.Hahn
