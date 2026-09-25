import Problib.Measure.Giry.Monad
import Problib.Measure.Kernel.Product

set_option autoImplicit false

namespace Problib.Measure.Giry

open Problib.Real

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {source : Space α} {target : Space β} {result : Space γ}

/-- Jointly parameterized bind: binding parameter-dependent prior laws against
a jointly measurable family is measurable in the parameter. -/
theorem bind_joint_measurable (prior : α → Law target)
    (priorMeasurable : MeasurableMap source (space target) prior)
    (family : α × β → Law result)
    (measurable : MeasurableMap (Space.product source target) (space result) family) :
    MeasurableMap source (space result)
      (fun point => bind (prior point) (fun value => family (point, value))
        (MeasurableMap.comp measurable (Kernel.pair_left_measurable point))) := by
  apply (measurable_iff _).mpr
  intro region regionMeasurable
  have integral := Kernel.lintegral_measurable_joint
    (toKernel prior priorMeasurable) (toKernel_finite prior priorMeasurable).toSFinite
    (function := fun point value => (family (point, value)).val region)
    ((measurable_iff family).mp measurable regionMeasurable)
  have equal : (fun point => (bind (prior point) (fun value => family (point, value))
        (MeasurableMap.comp measurable (Kernel.pair_left_measurable point))).val region) =
      (fun point => lintegral (prior point).val (fun value => (family (point, value)).val region)) := by
    funext point
    exact bind_apply _ _ _ regionMeasurable
  rw [equal]
  exact integral

/-- Measurability of binding a constant prior law against a jointly measurable
family in the parameter. -/
theorem bind_family_measurable (law : Law target)
    (family : α × β → Law result)
    (measurable : MeasurableMap (Space.product source target) (space result) family) :
    MeasurableMap source (space result)
      (fun point => bind law (fun value => family (point, value))
        (MeasurableMap.comp measurable (Kernel.pair_left_measurable point))) :=
  bind_joint_measurable (fun _ => law)
    (MeasurableMap.constant source (space target) law) family measurable

/-- Tensorial strength: pairs a parameter point with a probability law to form
a probability law on the product space. -/
noncomputable def strength (source : Space α) (target : Space β)
    (pair : α × Law target) : Law (Space.product source target) :=
  map (fun value => (pair.1, value)) (Kernel.pair_left_measurable pair.1) pair.2

/-- Tensorial strength is jointly measurable from `source × space target` to
`space (source × target)`. -/
theorem strength_measurable (source : Space α) (target : Space β) :
    MeasurableMap (Space.product source (space target))
      (space (Space.product source target)) (strength source target) := by
  apply (measurable_iff _).mpr
  intro region regionMeasurable
  let parameter := Space.product source (space target)
  let kernel := toKernel (fun pair : α × Law target => pair.2)
    (Space.second_measurable source (space target))
  have projection : MeasurableMap (Space.product parameter target)
      (Space.product source target) (fun point => (point.1.1, point.2)) :=
    Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable source (space target))
        (Space.first_measurable parameter target))
      (Space.second_measurable parameter target)
  have sections := Kernel.section_apply_measurable kernel
    (toKernel_finite _ _).toSFinite (projection regionMeasurable)
  have equal : (fun pair => (strength source target pair).val region) =
      (fun pair => kernel pair
        (Kernel.verticalSection (Set.preimage (fun point => (point.1.1, point.2)) region)
          pair)) := by
    funext pair
    exact pair.2.val.map_apply (fun value => (pair.1, value))
      (Kernel.pair_left_measurable pair.1) regionMeasurable
  rw [equal]
  exact sections

/-- Tensorial strength preserves the Dirac unit. -/
theorem strength_pure (point : α) (value : β) :
    strength source target (point, pure target value) =
      pure (Space.product source target) (point, value) :=
  map_pure (fun value => (point, value)) (Kernel.pair_left_measurable point) value

/-- Naturality of tensorial strength with respect to product pushforwards. -/
theorem strength_natural {other : Space δ} (point : α) (law : Law target)
    (first : α → γ) (firstMeasurable : MeasurableMap source result first)
    (second : β → δ) (secondMeasurable : MeasurableMap target other second) :
    map (fun pair => (first pair.1, second pair.2))
      (Space.product_map firstMeasurable secondMeasurable)
      (strength source target (point, law)) =
      strength result other (first point, map second secondMeasurable law) := by
  unfold strength
  rw [map_comp, map_comp] <;> exact Kernel.pair_left_measurable _

/-- Projecting the second component of strength recovers the target law. -/
theorem strength_second (point : α) (law : Law target) :
    map Prod.snd (Space.second_measurable source target)
      (strength source target (point, law)) = law := by
  unfold strength
  rw [map_comp]
  · exact map_id law
  · exact Kernel.pair_left_measurable _

/-- Left unit coherence of strength for the discrete unit space. -/
theorem strength_unit (law : Law target) :
    map Prod.snd (Space.second_measurable (Space.discrete Unit) target)
      (strength (Space.discrete Unit) target ((), law)) = law :=
  strength_second () law

/-- Associator coherence of strength with Cartesian product association. -/
theorem strength_associate (first : α) (second : β) (law : Law result) :
    map (fun pair => (pair.1.1, (pair.1.2, pair.2)))
      (Space.associate_measurable source target result)
      (strength (Space.product source target) result ((first, second), law)) =
      strength source (Space.product target result)
        (first, strength target result (second, law)) := by
  unfold strength
  rw [map_comp, map_comp] <;> exact Kernel.pair_left_measurable _

/-- Compatibility of tensorial strength with monadic bind. -/
theorem strength_bind (point : α) (law : Law target) (family : β → Law result)
    (measurable : MeasurableMap target (space result) family) :
    strength source result (point, bind law family measurable) =
      bind (strength source target (point, law))
        (fun pair => strength source result (pair.1, family pair.2))
        (MeasurableMap.comp (strength_measurable source result)
          (Space.pair_measurable (Space.first_measurable source target)
            (MeasurableMap.comp measurable (Space.second_measurable source target)))) :=
  (map_bind law family measurable (fun value => (point, value))
    (Kernel.pair_left_measurable point)).trans
    (bind_map law (fun value => (point, value)) (Kernel.pair_left_measurable point)
      (fun pair => strength source result (pair.1, family pair.2))
      (MeasurableMap.comp (strength_measurable source result)
        (Space.pair_measurable (Space.first_measurable source target)
          (MeasurableMap.comp measurable (Space.second_measurable source target))))).symm

/-- Compatibility of tensorial strength with monadic join. -/
theorem strength_join (point : α) (law : Law (space target)) :
    strength source target (point, join law) =
      join (map (strength source target) (strength_measurable source target)
        (strength source (space target) (point, law))) :=
  (strength_bind point law (fun value => value)
    (MeasurableMap.identity (space target))).trans
    (bind_eq_join_map (strength source (space target) (point, law))
      (strength source target) (strength_measurable source target))

end Problib.Measure.Giry
