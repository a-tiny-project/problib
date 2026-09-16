import Foundations.Measure.Giry.Strength

set_option autoImplicit false

namespace Foundations.Measure.Giry

open Foundations.Real

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  {source : Space α} {target : Space β} {result : Space γ}

/-- Tonelli integral swap for probability laws, using actual Tonelli with
finite integration premises discharged by total mass one. -/
theorem integral_swap (left : Law source) (right : Law target)
    {function : α × β → ENNReal}
    (measurable : ENNRealMeasurable (Space.product source target) function) :
    lintegral left.val (fun point => lintegral right.val (fun value => function (point, value))) =
      lintegral right.val (fun value => lintegral left.val (fun point => function (point, value))) :=
  (lintegral_prod left.val right.val (Measure.SFinite.ofFinite right.property.toFinite)
    measurable).symm.trans
    (lintegral_prod_symm left.val right.val (Measure.SFinite.ofFinite left.property.toFinite)
      (Measure.SFinite.ofFinite right.property.toFinite) measurable)

/-- Commutativity of independent monadic binds (Fubini exchange) for
probability laws. -/
theorem bind_comm (left : Law source) (right : Law target)
    (family : α × β → Law result)
    (measurable : MeasurableMap (Space.product source target) (space result) family) :
    bind left (fun point => bind right (fun value => family (point, value))
      (MeasurableMap.comp measurable (Kernel.pair_left_measurable point)))
      (bind_family_measurable right family measurable) =
    bind right (fun value => bind left (fun point => family (point, value))
      (MeasurableMap.comp measurable
        (MeasurableMap.comp (Space.swap_measurable target source)
          (Kernel.pair_left_measurable value))))
      (bind_family_measurable left (fun pair => family (pair.2, pair.1))
        (MeasurableMap.comp measurable (Space.swap_measurable target source))) := by
  apply ext
  intro region regionMeasurable
  rw [bind_apply _ _ _ regionMeasurable, bind_apply _ _ _ regionMeasurable]
  calc
    _ = lintegral left.val
        (fun point => lintegral right.val (fun value => (family (point, value)).val region)) := by
      apply lintegral_congr
      intro point
      exact bind_apply _ _ _ regionMeasurable
    _ = lintegral right.val
        (fun value => lintegral left.val (fun point => (family (point, value)).val region)) :=
      integral_swap left right ((measurable_iff family).mp measurable regionMeasurable)
    _ = _ := by
      apply lintegral_congr
      intro value
      exact (bind_apply _ _ _ regionMeasurable).symm

/-- Independent product of two probability laws constructed via strength and
monadic bind. -/
noncomputable def product (left : Law source) (right : Law target) :
    Law (Space.product source target) :=
  bind left (fun point => strength source target (point, right))
    (MeasurableMap.comp (strength_measurable source target)
      (Space.pair_measurable (MeasurableMap.identity source)
        (MeasurableMap.constant source (space target) right)))

/-- The independent product map on probability laws is jointly measurable. -/
theorem product_measurable (source : Space α) (target : Space β) :
    MeasurableMap (Space.product (space source) (space target))
      (space (Space.product source target)) (fun pair => product pair.1 pair.2) := by
  let parameter := Space.product (space source) (space target)
  exact @bind_joint_measurable (Law source × Law target) α (α × β)
    parameter source (Space.product source target)
    (fun pair : Law source × Law target => pair.1)
    (Space.first_measurable (space source) (space target))
    (fun pair : (Law source × Law target) × α => strength source target (pair.2, pair.1.2))
    (MeasurableMap.comp (strength_measurable source target)
      (Space.pair_measurable (Space.second_measurable parameter source)
        (MeasurableMap.comp (Space.second_measurable (space source) (space target))
          (Space.first_measurable parameter source))))

/-- The measure underlying the Giry product law is the exact product
measure. -/
theorem product_measure (left : Law source) (right : Law target) :
    (product left right).val =
      Measure.prod left.val right.val (Measure.SFinite.ofFinite right.property.toFinite) := rfl

/-- Evaluation of a product law on measurable rectangles equals the product
of individual evaluations. -/
theorem product_apply (left : Law source) (right : Law target)
    {leftRegion : Set α} {rightRegion : Set β}
    (leftMeasurable : source.Measurable leftRegion)
    (rightMeasurable : target.Measurable rightRegion) :
    (product left right).val (Set.product leftRegion rightRegion) =
      ENNReal.mul (left.val leftRegion) (right.val rightRegion) :=
  Measure.prod_apply_product left.val right.val
    (Measure.SFinite.ofFinite right.property.toFinite) leftMeasurable rightMeasurable

/-- Commutative coordinate swap symmetry of the Giry product law. -/
theorem product_swap (left : Law source) (right : Law target) :
    map (fun pair => (pair.2, pair.1)) (Space.swap_measurable source target)
      (product left right) = product right left :=
  Subtype.ext (Measure.prod_swap_of_finite left.property.toFinite right.property.toFinite)

end Foundations.Measure.Giry
