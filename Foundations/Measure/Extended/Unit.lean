module

public import Foundations.Measure.Extended.Conversion
public import Foundations.Measure.Extended.Algebra.Binary

/-!
# Unit interval clamping for extended nonnegative reals

This module defines the canonical clamping retraction from extended
nonnegative reals to the closed unit interval.
The operation is monotone, measurable, and maps infinity to unit one.
-/

set_option autoImplicit false

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

/-- Clamp an extended nonnegative real into the unit interval by mapping
values above one and infinity to one. -/
@[expose] public noncomputable def unitClamp (value : ENNReal) : UnitInterval :=
  ⟨ENNReal.toReal (ENNReal.min value ENNReal.one),
    ENNReal.toRealNonnegative _, by
      have bound := (ENNReal.toRealLeToRealIff (right := ENNReal.one)
        (ENNReal.finiteOfLe (ENNReal.minLeRight value ENNReal.one) True.intro)
        True.intro).mpr (ENNReal.minLeRight value ENNReal.one)
      exact bound⟩

/-- The extended-real embedding of a clamped value equals the minimum of the
input and one. -/
public theorem ofReal_unitClamp (value : ENNReal) :
    ENNReal.ofReal (unitClamp value).val = ENNReal.min value ENNReal.one :=
  ENNReal.ofRealToReal
    (ENNReal.finiteOfLe (ENNReal.minLeRight value ENNReal.one) True.intro)

/-- The extended-real embedding of a clamped value preserves any input
already bounded by one. -/
public theorem ofReal_unitClamp_of_le {value : ENNReal} (bound : ENNReal.le value ENNReal.one) :
    ENNReal.ofReal (unitClamp value).val = value := by
  rw [ofReal_unitClamp, ENNReal.minEqLeft bound]

/-- Clamping retracts the canonical embedding of the unit interval into
extended nonnegative reals. -/
public theorem unitClamp_ofReal (value : UnitInterval) :
    unitClamp (ENNReal.ofReal value.val) = value := by
  apply Subtype.ext
  have bound : ENNReal.le (ENNReal.ofReal value.val) ENNReal.one := by
    exact (ENNReal.ofRealLeIffLeToReal (upper := ENNReal.one) True.intro).mpr value.property.2
  change ENNReal.toReal (ENNReal.min (ENNReal.ofReal value.val) ENNReal.one) = value.val
  rw [ENNReal.minEqLeft bound, ENNReal.toRealOfReal value.property.1]

/-- Clamping maps top to the unit upper bound one. -/
public theorem unitClamp_top : unitClamp ENNReal.top = unitOne := by
  apply Subtype.ext
  change ENNReal.toReal (ENNReal.min ENNReal.top ENNReal.one) = Dedekind.one
  rw [ENNReal.minEqRight (ENNReal.leTop _), ENNReal.toRealOne]

/-- Clamping preserves the canonical order from extended nonnegative reals
to Dedekind reals. -/
public theorem unitClamp_mono {left right : ENNReal} (included : ENNReal.le left right) :
    Dedekind.le (unitClamp left).val (unitClamp right).val := by
  apply (ENNReal.toRealLeToRealIff
    (ENNReal.finiteOfLe (ENNReal.minLeRight left ENNReal.one) True.intro)
    (ENNReal.finiteOfLe (ENNReal.minLeRight right ENNReal.one) True.intro)).mpr
  exact ENNReal.leMin (ENNReal.leTrans (ENNReal.minLeLeft left ENNReal.one) included)
    (ENNReal.minLeRight left ENNReal.one)

/-- Clamping is a measurable map from the extended-real Borel space to the
unit-interval Borel space. -/
public theorem unitClampMeasurable : MeasurableMap ennrealBorel unitBorel unitClamp := by
  have minimum := ENNRealMeasurable.min ENNRealMeasurable.identity
    (ENNRealMeasurable.constant ennrealBorel ENNReal.one)
  have inclusion : MeasurableMap ennrealBorel borel
      (fun value => ENNReal.toReal (ENNReal.min value ENNReal.one)) :=
    MeasurableMap.comp toRealMeasurable minimum.measurableMap
  apply measurableMap_unitBorel_iff_Iio.mpr
  intro upper
  exact inclusion (measurable_Iio upper)

end Foundations.Measure.Real
