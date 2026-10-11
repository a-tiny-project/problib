module

public import Problib.Measure.Uniform
public import Problib.Measure.Real.Lebesgue
public import Problib.Measure.Real.Affine
public import Problib.Measure.Real.Order
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Integral.Density.Algebra

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real

/-- Unit-interval singletons are measurable in the pullback Borel space. -/
public theorem unit_singleton_measurable (point : UnitInterval) :
    unitBorel.Measurable (Set.singleton point) := by
  apply (Space.comap_measurable_iff unitInclusion borel _).mpr
  refine ⟨Set.singleton point.val, measurable_singleton point.val, ?_⟩
  apply Set.ext
  intro value
  exact ⟨fun equal => congrArg Subtype.val equal,
    fun equal => Subtype.ext equal⟩

/-- Equality of the two unit coordinates is a product-measurable set. -/
public theorem unit_diagonal_measurable :
    (Space.product unitBorel unitBorel).Measurable
      (fun pair : UnitInterval × UnitInterval => pair.1 = pair.2) := by
  have valuesMeasurable := measurable_eq
    (MeasurableMap.comp unitInclusion_measurable
      (Space.first_measurable unitBorel unitBorel))
    (MeasurableMap.comp unitInclusion_measurable
      (Space.second_measurable unitBorel unitBorel))
  have same : (fun pair : UnitInterval × UnitInterval => pair.1 = pair.2) =
      (fun pair => pair.1.val = pair.2.val) := by
    apply Set.ext
    intro pair
    exact ⟨fun equal => congrArg Subtype.val equal,
      fun equal => Subtype.ext equal⟩
  rw [same]
  exact valuesMeasurable

/-- Existing `uniform01_map_unitInclusion` identifies the uniform law
with volume restricted to the closed unit interval. -/
public theorem uniform01_volume_density :
    Measure.IsDensity (uniform01.map unitInclusion unitInclusion_measurable)
      volume (fun x => ennrealIndicator unitSet (fun _ => ENNReal.one) x) := by
  rw [uniform01_map_unitInclusion]
  change restrictedUnit = volume.withDensity
    (ennrealIndicator unitSet (fun _ => ENNReal.one))
  rw [restrictedUnit,
    volume.withDensity_indicator (fun _ => ENNReal.one)
      (show borel.Measurable unitSet from measurable_icc _ _),
    (volume.restrict unitSet).withDensity_one]

/-- The diagonal inside the unit square is null for the product uniform law. -/
public theorem uniform01_prod_diagonal_null
    (finite : Measure.SFinite uniform01) :
    (Measure.prod uniform01 uniform01 finite).NullSet
      (fun pair => pair.1 = pair.2) := by
  let diagonal : Set (UnitInterval × UnitInterval) :=
    fun pair => pair.1 = pair.2
  have diagonalMeasurable :
      (Space.product unitBorel unitBorel).Measurable diagonal :=
    unit_diagonal_measurable
  change (Measure.prod uniform01 uniform01 finite) diagonal = ENNReal.zero
  rw [Measure.prod_apply uniform01 uniform01 finite diagonalMeasurable]
  have sectionEq (point : UnitInterval) :
      Set.preimage (fun value => (point, value)) diagonal =
        Set.singleton point := by
    apply Set.ext
    intro value
    exact ⟨fun equal => equal.symm, fun equal => equal.symm⟩
  have zero : (fun point => uniform01
      (Set.preimage (fun value => (point, value)) diagonal)) =
      (fun _ => ENNReal.zero) := by
    funext point
    rw [sectionEq]
    exact uniform01_singleton point
  rw [zero]
  exact lintegral_zero uniform01

end Problib.Measure.Real
