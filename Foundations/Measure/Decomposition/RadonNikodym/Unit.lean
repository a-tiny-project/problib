module

public import Foundations.Measure.Decomposition.RadonNikodym.SFinite
public import Foundations.Measure.Decomposition.RadonNikodym.Order
public import Foundations.Measure.Integral.Density.Unit

/-!
# Measurable unit densities under domination

This module constructs measurable unit-interval densities for target
measures dominated by a sigma-finite reference on measurable sets.
The construction selects an s-finite Radon-Nikodym derivative and clamps
values to the unit interval.
The density reconstructs the target measure and respects measure order on
countable families outside a single reference-null set.
-/

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real
open Foundations.Real.Construction

universe u

variable {alpha : Type u} {space : Space alpha}
  {target reference : Measure space}

private noncomputable def dominatedDerivative (finite : SigmaFinite reference)
    (included : ∀ set, space.Measurable set → ENNReal.le (target set) (reference set)) :
    RadonNikodymDerivative target reference :=
  RadonNikodymDerivative.ofSFinite (finite.of_le included).toSFinite finite
    (AbsolutelyContinuous.of_le (AbsolutelyContinuous.refl reference) included)

/-- Construct a measurable unit-interval density for a target measure
dominated by a sigma-finite reference on measurable sets. -/
public noncomputable def unitDensity (finite : SigmaFinite reference)
    (included : ∀ set, space.Measurable set → ENNReal.le (target set) (reference set)) :
    alpha → Real.UnitInterval :=
  fun value => Real.unitClamp ((dominatedDerivative finite included).density value)

/-- The constructed unit density is measurable from the ambient space to the
unit-interval Borel space. -/
public theorem unitDensity_measurable (finite : SigmaFinite reference)
    (included : ∀ set, space.Measurable set → ENNReal.le (target set) (reference set)) :
    MeasurableMap space Real.unitBorel (unitDensity finite included) :=
  MeasurableMap.comp Real.unitClampMeasurable
    (dominatedDerivative finite included).densityMeasurable.measurableMap

/-- The constructed unit density reconstructs the target measure as the
weighted density integral against the reference measure. -/
public theorem unitDensity_reconstruct (finite : SigmaFinite reference)
    (included : ∀ set, space.Measurable set → ENNReal.le (target set) (reference set)) :
    IsDensity target reference (fun value => ENNReal.ofReal (unitDensity finite included value).val) := by
  let derivative := dominatedDerivative finite included
  have bound := (derivative.density_ae_le_one_iff finite).mpr included
  have equal : reference.AEEq (fun value => ENNReal.ofReal (unitDensity finite included value).val)
      derivative.density :=
    bound.mono (fun _ member => Real.ofReal_unitClamp_of_le member)
  exact derivative.reconstruct_eq.trans (withDensity_congr_ae equal).symm

/-- Characterize existence of a measurable unit density.
Under a sigma-finite reference, existence is equivalent to whole-measure
domination on all measurable sets. -/
public theorem exists_unitDensity_iff (finite : SigmaFinite reference) :
    (∃ density : alpha → Real.UnitInterval,
      MeasurableMap space Real.unitBorel density ∧
        IsDensity target reference (fun value => ENNReal.ofReal (density value).val)) ↔
      ∀ set, space.Measurable set → ENNReal.le (target set) (reference set) := by
  constructor
  · rintro ⟨density, _, reconstruct⟩ set _
    exact reconstruct.le_of_unit set
  · intro included
    exact ⟨unitDensity finite included, unitDensity_measurable finite included,
      unitDensity_reconstruct finite included⟩

/-- Pairwise measure domination implies almost-everywhere pointwise order of
the corresponding unit densities under the sigma-finite reference measure. -/
public theorem unitDensity_ae_mono {left right : Measure space}
    (finite : SigmaFinite reference)
    (leftBound : ∀ set, space.Measurable set → ENNReal.le (left set) (reference set))
    (rightBound : ∀ set, space.Measurable set → ENNReal.le (right set) (reference set))
    (included : ∀ set, space.Measurable set → ENNReal.le (left set) (right set)) :
    reference.AE (fun value => Dedekind.le
      (unitDensity finite leftBound value).val (unitDensity finite rightBound value).val) :=
  ((unitDensity_reconstruct finite leftBound).unit_ae_le_iff
    (unitDensity_reconstruct finite rightBound)
    (unitDensity_measurable finite leftBound) (unitDensity_measurable finite rightBound)
    finite).mpr included

/-- Sequence-indexed order coherence outside a single reference-null set.
Every measure-order relation in the family simultaneously implies pointwise
inequality of the constructed unit densities. -/
public theorem unitDensity_ae_all_order {measures : Nat → Measure space}
    (finite : SigmaFinite reference)
    (bounded : ∀ index set, space.Measurable set →
      ENNReal.le (measures index set) (reference set)) :
    reference.AE (fun value => ∀ first second,
      (∀ set, space.Measurable set → ENNReal.le (measures first set) (measures second set)) →
        Dedekind.le (unitDensity finite (bounded first) value).val
          (unitDensity finite (bounded second) value).val) := by
  apply ae_all_iff.mpr
  intro first
  apply ae_all_iff.mpr
  intro second
  classical
  by_cases included : ∀ set, space.Measurable set →
      ENNReal.le (measures first set) (measures second set)
  · exact (unitDensity_ae_mono finite (bounded first) (bounded second) included).mono
      (fun _ holds _ => holds)
  · exact ae_of_forall (fun _ impossible => False.elim (included impossible))

end Foundations.Measure.Measure
