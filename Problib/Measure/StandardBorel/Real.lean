module

public import Problib.Measure.StandardBorel.Basic
public import Problib.Measure.StandardBorel.Real.Coordinate

set_option autoImplicit false

namespace Problib.Measure.StandardBorel

open Problib.Measure.Real
open Problib.Real.Construction.Dedekind

/-- Standard-Borel presentation of the real Borel space through the
order-preserving bijection with the open unit interval. -/
@[expose] public noncomputable def real : StandardBorel borel := by
  let range : Set UnitInterval := fun point => Ioo zero one point.val
  let forward : Carrier → {point : UnitInterval // range point} := fun value =>
    ⟨⟨Real.encode value, (Real.encode_mem value).left.left,
      (Real.encode_mem value).right.left⟩, Real.encode_mem value⟩
  let backward : {point : UnitInterval // range point} → Carrier := fun point =>
    Real.decode point.val.val
  have coordinateMeasurable : MeasurableMap borel borel Real.encode :=
    monotone_measurable (fun {_ _} included => Real.encode_monotone included)
  have unitMeasurable :
      MeasurableMap borel unitBorel (fun value => (forward value).val) := by
    apply measurableMap_unitBorel_iff_iio.mpr
    intro upper
    exact coordinateMeasurable (measurable_iio upper)
  have forwardMeasurable : MeasurableMap borel
      (Space.comap (fun point : {value : UnitInterval // range value} => point.val)
        unitBorel) forward := by
    intro region measurable
    rcases (Space.comap_measurable_iff _ unitBorel region).mp measurable with
      ⟨target, targetMeasurable, rfl⟩
    exact unitMeasurable targetMeasurable
  have backwardMeasurable : MeasurableMap
      (Space.comap (fun point : {value : UnitInterval // range value} => point.val)
        unitBorel) borel backward := by
    apply monotone_pullback_measurable
      (coordinate := fun point => point.val.val)
    · exact MeasurableMap.comp unitInclusion_measurable (Space.comap_map _ unitBorel)
    · intro left right included
      exact Real.decode_monotone left.property right.property included
  exact {
    range := range
    range_measurable := unitInclusion_measurable (measurable_ioo zero one)
    equivalence := {
      forward := forward
      inverse := backward
      inverse_forward := Real.decode_encode
      forward_inverse := by
        intro point
        apply Subtype.ext
        apply Subtype.ext
        exact Real.encode_decode point.val.val point.property
      forward_measurable := forwardMeasurable
      inverse_measurable := backwardMeasurable
    }
  }

end Problib.Measure.StandardBorel
