module

public import Problib.Measure.Integral.Density.Order
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Extended.Unit

/-!
# Unit-interval density domination and comparison

This module proves measure domination and order comparison for generic
unit-interval density representatives.
-/

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real
open Problib.Real.Construction

universe u

variable {alpha : Type u} {space : Space alpha}
  {target reference : Measure space}

/-- Having a unit-interval density implies domination on all sets.
This implication requires no reference finiteness or density measurability
hypotheses. -/
public theorem IsDensity.le_of_unit {density : alpha → Real.UnitInterval}
    (reconstruct : IsDensity target reference (fun value => ENNReal.ofReal (density value).val))
    (set : Set alpha) : ENNReal.le (target set) (reference set) := by
  have bound : reference.AE (fun value =>
      ENNReal.le (ENNReal.ofReal (density value).val) ENNReal.one) :=
    ae_of_forall (fun value => (ENNReal.ofReal_le_iff_le_toReal
      (upper := ENNReal.one) True.intro).mpr (density value).property.2)
  have comparison := withDensity_mono_ae bound set
  rw [← reconstruct.eq_withDensity, reference.withDensity_one] at comparison
  exact comparison

/-- Compare two measurable unit densities under a sigma-finite reference.
Almost-everywhere pointwise order is equivalent to whole-measure domination
on all measurable sets. -/
public theorem IsDensity.unit_ae_le_iff {left right : Measure space}
    {first second : alpha → Real.UnitInterval}
    (firstDensity : IsDensity left reference (fun value => ENNReal.ofReal (first value).val))
    (secondDensity : IsDensity right reference (fun value => ENNReal.ofReal (second value).val))
    (firstMeasurable : MeasurableMap space Real.unitBorel first)
    (secondMeasurable : MeasurableMap space Real.unitBorel second)
    (finite : SigmaFinite reference) :
    reference.AE (fun value => Dedekind.le (first value).val (second value).val) ↔
      ∀ set, space.Measurable set → ENNReal.le (left set) (right set) := by
  have firstExtended : ENNRealMeasurable space
      (fun value => ENNReal.ofReal (first value).val) := Real.ofReal_measurable.comp
    (MeasurableMap.comp Real.unitInclusion_measurable firstMeasurable)
  have secondExtended : ENNRealMeasurable space
      (fun value => ENNReal.ofReal (second value).val) := Real.ofReal_measurable.comp
    (MeasurableMap.comp Real.unitInclusion_measurable secondMeasurable)
  have comparison := withDensity_le_iff_ae_le finite firstExtended secondExtended
  rw [← firstDensity.eq_withDensity, ← secondDensity.eq_withDensity] at comparison
  exact Iff.trans
    ⟨fun holds => holds.mono (fun value included =>
        (ENNReal.ofReal_le_ofReal_iff (first value).property.1 (second value).property.1).mpr included),
      fun holds => holds.mono (fun value included =>
        (ENNReal.ofReal_le_ofReal_iff (first value).property.1 (second value).property.1).mp included)⟩
    comparison.symm

end Problib.Measure.Measure
