module

public import Problib.Measure.Memo.Query
public import Problib.Measure.Extended.Unit

set_option autoImplicit false

namespace Problib.Measure.Memo
public section
open Problib.Real Problib.Measure.Real

theorem law_coordinate_true (bias : Bias) (key : Nat) :
    law bias (fun table => table key = true) = ENNReal.ofReal (bias key).val := by
  have equal : Cylinder (Cache.insert [] key true) = (fun table => table key = true) := by
    rw [Cache.cylinder_insert true rfl]
    apply Set.ext; intro table; exact ⟨And.right, fun h => ⟨trivial, h⟩⟩
  rw [← equal, law_cylinder, Cache.weight_insert bias true rfl, cacheWeight, ENNReal.one_mul]
  rfl

universe u v
variable {α : Type u} {κ : Type v} {source : Space α} {keySpace : Space κ}

@[expose] noncomputable def bodyBias
    (body : Kernel (Space.product keySpace source) (Space.discrete Bool)) : α → κ → UnitInterval :=
  fun input key => unitClamp (body (key, input) (Set.singleton true))

theorem bodyBias_measurable
    (body : Kernel (Space.product keySpace source) (Space.discrete Bool)) (key : κ) :
    MeasurableMap source unitBorel (fun input => bodyBias body input key) :=
  MeasurableMap.comp unitClamp_measurable
    (MeasurableMap.comp (body.measurable (Space.discrete_measurable (Set.singleton true))).measurableMap
      (Space.pair_measurable (MeasurableMap.constant _ _ key) (MeasurableMap.identity _)))

end
end Problib.Measure.Memo
