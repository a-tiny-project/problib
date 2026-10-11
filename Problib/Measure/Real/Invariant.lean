module

public import Problib.Measure.Real.Pi
public import Problib.Measure.Real.Arithmetic
public import Problib.Real.Grind

set_option autoImplicit false

/-! Volumes invariant under translation and negation, and shears of products.

A shear moves one coordinate of a pair by an amount that depends only on the
other. Within each fiber it is a map of one factor, so when that map preserves
the factor, Tonelli carries the fiberwise fact to the product
(`prod_map_fiber`, and `prod_map_fiber_first` for the other coordinate).

`InvariantVolume` is the structure a shear by translation needs: an addition
and a negation on a space, the three laws that make translation undo itself
through negation, and a measure that translation and negation preserve.
Lebesgue measure on a line is one (`InvariantVolume.real`), a product of two
is one (`InvariantVolume.product`), and the finite product `volumePi n` is one
(`InvariantVolume.pi`). Nothing here names an integrator; the leapfrog
integrator in `Inference/Leapfrog.lean` is written once over this structure. -/

namespace Problib.Measure

open Problib.Real
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel volume volumeSFinite map_volume_translate
  map_volume_neg translate_measurable neg_measurable measurable_add volumePi volumePiSFinite
  translatePi translatePi_measurable map_volumePi_translate negPi negPi_measurable
  map_volumePi_neg)

universe u v
variable {α : Type u} {β : Type v} {left : Space α} {right : Space β}

public section

/-! ### Shears preserve product measures -/

/-- A map that moves only the second coordinate, and preserves the second
factor within each fiber, preserves the product. -/
theorem prod_map_fiber (first : Measure left) (second : Measure right)
    (secondFinite : Measure.SFinite second) (shift : α → β → β)
    (measurable : MeasurableMap (Space.product left right) (Space.product left right)
      (fun pair => (pair.1, shift pair.1 pair.2)))
    (preserves : ∀ point set, right.Measurable set →
      second (Set.preimage (shift point) set) = second set) :
    (Measure.prod first second secondFinite).map
        (fun pair => (pair.1, shift pair.1 pair.2)) measurable =
      Measure.prod first second secondFinite := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.map_apply _ _ _ setMeasurable,
    Measure.prod_apply _ _ _ (measurable setMeasurable),
    Measure.prod_apply _ _ _ setMeasurable]
  apply lintegral_congr
  intro point
  exact preserves point _ (Kernel.verticalSection_measurable setMeasurable point)

/-- A map that moves only the first coordinate, and preserves the first factor
within each fiber, preserves the product. It is `prod_map_fiber` read through
the swap of factors. -/
theorem prod_map_fiber_first (first : Measure left) (second : Measure right)
    (firstFinite : Measure.SFinite first) (secondFinite : Measure.SFinite second)
    (shift : β → α → α)
    (measurable : MeasurableMap (Space.product left right) (Space.product left right)
      (fun pair => (shift pair.2 pair.1, pair.2)))
    (preserves : ∀ point set, left.Measurable set →
      first (Set.preimage (shift point) set) = first set) :
    (Measure.prod first second secondFinite).map
        (fun pair => (shift pair.2 pair.1, pair.2)) measurable =
      Measure.prod first second secondFinite := by
  have swapped : MeasurableMap (Space.product right left) (Space.product right left)
      (fun pair => (pair.1, shift pair.1 pair.2)) :=
    MeasurableMap.comp (Space.swap_measurable left right)
      (MeasurableMap.comp measurable (Space.swap_measurable right left))
  rw [← Measure.prod_swap secondFinite firstFinite, Measure.map_comp]
  calc
    (Measure.prod second first firstFinite).map _ _ =
        ((Measure.prod second first firstFinite).map
          (fun pair => (pair.1, shift pair.1 pair.2)) swapped).map
          (fun pair => (pair.2, pair.1)) (Space.swap_measurable right left) := by
      rw [Measure.map_comp]
    _ = (Measure.prod second first firstFinite).map
          (fun pair => (pair.2, pair.1)) (Space.swap_measurable right left) := by
      rw [prod_map_fiber second first firstFinite shift swapped preserves]

/-- A map that preserves a measure's value on every measurable set preserves the
measure. -/
theorem map_eq_of_preimage {measure : Measure left} {map : α → α}
    (measurable : MeasurableMap left left map)
    (preserves : ∀ set, left.Measurable set → measure (Set.preimage map set) = measure set) :
    measure.map map measurable = measure := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.map_apply _ _ _ setMeasurable]
  exact preserves set setMeasurable

/-- A measure preserved by a map gives each measurable set's preimage the set's
measure. -/
theorem preimage_of_map_eq {measure : Measure left} {map : α → α}
    (measurable : MeasurableMap left left map) (preserved : measure.map map measurable = measure)
    {set : Set α} (setMeasurable : left.Measurable set) :
    measure (Set.preimage map set) = measure set := by
  rw [← Measure.map_apply _ _ measurable setMeasurable, preserved]

/-! ### Invariant volumes -/

/-- A measure on a space with an addition and a negation, preserved by every
translation and by negation. The three laws are the ones reversing a shear
through a negation reads: a translation undone by the negated shift, negation
distributing over addition, and negation an involution. -/
structure InvariantVolume (space : Space α) where
  add : α → α → α
  neg : α → α
  addMeasurable : MeasurableMap (Space.product space space) space (fun pair => add pair.1 pair.2)
  negMeasurable : MeasurableMap space space neg
  add_neg_cancel_right : ∀ point shift, add (add point shift) (neg shift) = point
  neg_add : ∀ first second, neg (add first second) = add (neg first) (neg second)
  neg_neg : ∀ point, neg (neg point) = point
  measure : Measure space
  finite : Measure.SFinite measure
  translate : ∀ shift set, space.Measurable set →
    measure (Set.preimage (fun point => add point shift) set) = measure set
  reflect : ∀ set, space.Measurable set → measure (Set.preimage neg set) = measure set

namespace InvariantVolume

variable {space : Space α}

/-- Translation by a constant on the right is measurable. -/
theorem translate_measurable (volume : InvariantVolume space) (shift : α) :
    MeasurableMap space space (fun point => volume.add point shift) :=
  MeasurableMap.comp volume.addMeasurable
    (Space.pair_measurable (MeasurableMap.identity space) (MeasurableMap.constant space space shift))

/-- Translation preserves the volume. -/
theorem map_translate (volume : InvariantVolume space) (shift : α) :
    volume.measure.map (fun point => volume.add point shift)
      (volume.translate_measurable shift) = volume.measure :=
  map_eq_of_preimage _ (volume.translate shift)

/-- Negation preserves the volume. -/
theorem map_neg (volume : InvariantVolume space) :
    volume.measure.map volume.neg volume.negMeasurable = volume.measure :=
  map_eq_of_preimage _ volume.reflect

/-- Lebesgue measure on the line. -/
@[expose] noncomputable def real : InvariantVolume borel where
  add := Dedekind.add
  neg := Dedekind.neg
  addMeasurable := measurable_add (Space.first_measurable _ _) (Space.second_measurable _ _)
  negMeasurable := neg_measurable
  add_neg_cancel_right _ _ := by real_grind
  neg_add _ _ := by real_grind
  neg_neg _ := by real_grind
  measure := volume
  finite := volumeSFinite
  translate shift set setMeasurable := by
    have same : Set.preimage (fun value => Dedekind.add value shift) set =
        Set.preimage (Dedekind.add shift) set :=
      Set.ext fun value => Iff.of_eq (congrArg set (Dedekind.add_comm value shift))
    rw [same, ← Measure.map_apply _ _ (Problib.Measure.Real.translate_measurable shift)
      setMeasurable, map_volume_translate]
  reflect set setMeasurable := by
    rw [← Measure.map_apply _ _ neg_measurable setMeasurable, map_volume_neg]

/-- Two invariant volumes make one on the product, coordinatewise. -/
@[expose] noncomputable def product {secondSpace : Space β} (first : InvariantVolume space)
    (second : InvariantVolume secondSpace) : InvariantVolume (Space.product space secondSpace) where
  add left right := (first.add left.1 right.1, second.add left.2 right.2)
  neg point := (first.neg point.1, second.neg point.2)
  addMeasurable := Space.pair_measurable
    (MeasurableMap.comp first.addMeasurable (Space.product_map
      (Space.first_measurable _ _) (Space.first_measurable _ _)))
    (MeasurableMap.comp second.addMeasurable (Space.product_map
      (Space.second_measurable _ _) (Space.second_measurable _ _)))
  negMeasurable := Space.product_map first.negMeasurable second.negMeasurable
  add_neg_cancel_right point shift := by
    change (first.add (first.add point.1 shift.1) (first.neg shift.1),
      second.add (second.add point.2 shift.2) (second.neg shift.2)) = point
    rw [first.add_neg_cancel_right, second.add_neg_cancel_right]
  neg_add left right := by
    change (first.neg (first.add left.1 right.1), second.neg (second.add left.2 right.2)) = _
    rw [first.neg_add, second.neg_add]
  neg_neg point := by
    change (first.neg (first.neg point.1), second.neg (second.neg point.2)) = point
    rw [first.neg_neg, second.neg_neg]
  measure := Measure.prod first.measure second.measure second.finite
  finite := Measure.SFinite.prod first.finite second.finite
  translate shift set setMeasurable := by
    refine preimage_of_map_eq
      (Space.product_map (first.translate_measurable shift.1)
        (second.translate_measurable shift.2)) ?_ setMeasurable
    rw [Measure.prod_map first.measure second.measure second.finite _ _
      (first.translate_measurable shift.1) (second.translate_measurable shift.2)]
    rw [Measure.prod_congr_right _ _ second.finite (second.map_translate shift.2)]
    rw [first.map_translate]
  reflect set setMeasurable := by
    refine preimage_of_map_eq (Space.product_map first.negMeasurable second.negMeasurable) ?_
      setMeasurable
    rw [Measure.prod_map first.measure second.measure second.finite _ _
      first.negMeasurable second.negMeasurable]
    rw [Measure.prod_congr_right _ _ second.finite second.map_neg]
    rw [first.map_neg]

/-- Lebesgue measure on `dimension` coordinates, `volumePi`, with coordinatewise
addition and negation. -/
@[expose] noncomputable def pi (dimension : Nat) :
    InvariantVolume (Space.pi (fun _ : Fin dimension => borel)) where
  add left right index := Dedekind.add (left index) (right index)
  neg := negPi dimension
  addMeasurable := Space.pi_measurable fun index =>
    measurable_add
      (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin dimension => borel) index)
        (Space.first_measurable (Space.pi (fun _ : Fin dimension => borel))
          (Space.pi (fun _ : Fin dimension => borel))))
      (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin dimension => borel) index)
        (Space.second_measurable (Space.pi (fun _ : Fin dimension => borel))
          (Space.pi (fun _ : Fin dimension => borel))))
  negMeasurable := negPi_measurable dimension
  add_neg_cancel_right point shift := by
    funext index
    change Dedekind.add (Dedekind.add (point index) (shift index)) (Dedekind.neg (shift index)) =
      point index
    real_grind
  neg_add left right := by
    funext index
    change Dedekind.neg (Dedekind.add (left index) (right index)) =
      Dedekind.add (Dedekind.neg (left index)) (Dedekind.neg (right index))
    real_grind
  neg_neg point := by
    funext index
    change Dedekind.neg (Dedekind.neg (point index)) = point index
    real_grind
  measure := volumePi dimension
  finite := volumePiSFinite dimension
  translate shift set setMeasurable := by
    have same : Set.preimage (fun point index => Dedekind.add (point index) (shift index)) set =
        Set.preimage (translatePi dimension shift) set := by
      apply Set.ext
      intro point
      apply Iff.of_eq
      apply congrArg set
      funext index
      exact Dedekind.add_comm (point index) (shift index)
    rw [same, ← Measure.map_apply _ _ (translatePi_measurable dimension shift) setMeasurable,
      map_volumePi_translate]
  reflect set setMeasurable := by
    rw [← Measure.map_apply _ _ (negPi_measurable dimension) setMeasurable, map_volumePi_neg]

/-- An invariant volume carried along a measurable bijection with a
measurable inverse: addition and negation are read through the inverse, and
the measure is pushed forward. -/
@[expose] noncomputable def transport {target : Space β} (volume : InvariantVolume space)
    (forward : α → β) (backward : β → α)
    (forwardMeasurable : MeasurableMap space target forward)
    (backwardMeasurable : MeasurableMap target space backward)
    (backward_forward : ∀ point, backward (forward point) = point)
    (forward_backward : ∀ point, forward (backward point) = point) : InvariantVolume target where
  add left right := forward (volume.add (backward left) (backward right))
  neg point := forward (volume.neg (backward point))
  addMeasurable := MeasurableMap.comp forwardMeasurable
    (MeasurableMap.comp volume.addMeasurable
      (Space.product_map backwardMeasurable backwardMeasurable))
  negMeasurable := MeasurableMap.comp forwardMeasurable
    (MeasurableMap.comp volume.negMeasurable backwardMeasurable)
  add_neg_cancel_right point shift := by
    change forward (volume.add (backward (forward (volume.add (backward point) (backward shift))))
      (backward (forward (volume.neg (backward shift))))) = point
    rw [backward_forward, backward_forward, volume.add_neg_cancel_right, forward_backward]
  neg_add left right := by
    change forward (volume.neg (backward (forward (volume.add (backward left) (backward right))))) =
      forward (volume.add (backward (forward (volume.neg (backward left))))
        (backward (forward (volume.neg (backward right)))))
    rw [backward_forward, backward_forward, backward_forward, volume.neg_add]
  neg_neg point := by
    change forward (volume.neg (backward (forward (volume.neg (backward point))))) = point
    rw [backward_forward, volume.neg_neg, forward_backward]
  measure := volume.measure.map forward forwardMeasurable
  finite := volume.finite.map forward forwardMeasurable
  translate shift set setMeasurable := by
    have same : Set.preimage forward (Set.preimage
          (fun point => forward (volume.add (backward point) (backward shift))) set) =
        Set.preimage (fun point => volume.add point (backward shift))
          (Set.preimage forward set) :=
      Set.ext fun point => Iff.of_eq (by
        change set (forward (volume.add (backward (forward point)) (backward shift))) =
          set (forward (volume.add point (backward shift)))
        rw [backward_forward])
    change volume.measure.map forward forwardMeasurable _ =
      volume.measure.map forward forwardMeasurable set
    have translated : MeasurableMap target target
        (fun point => forward (volume.add (backward point) (backward shift))) :=
      MeasurableMap.comp forwardMeasurable (MeasurableMap.comp (volume.translate_measurable _)
        backwardMeasurable)
    rw [Measure.map_apply _ _ _ (translated setMeasurable), Measure.map_apply _ _ _ setMeasurable,
      same]
    exact volume.translate _ _ (forwardMeasurable setMeasurable)
  reflect set setMeasurable := by
    have same : Set.preimage forward (Set.preimage
          (fun point => forward (volume.neg (backward point))) set) =
        Set.preimage volume.neg (Set.preimage forward set) :=
      Set.ext fun point => Iff.of_eq (by
        change set (forward (volume.neg (backward (forward point)))) =
          set (forward (volume.neg point))
        rw [backward_forward])
    have negated : MeasurableMap target target
        (fun point => forward (volume.neg (backward point))) :=
      MeasurableMap.comp forwardMeasurable
        (MeasurableMap.comp volume.negMeasurable backwardMeasurable)
    change volume.measure.map forward forwardMeasurable _ =
      volume.measure.map forward forwardMeasurable set
    rw [Measure.map_apply _ _ _ (negated setMeasurable), Measure.map_apply _ _ _ setMeasurable,
      same]
    exact volume.reflect _ (forwardMeasurable setMeasurable)

end InvariantVolume

end

end Problib.Measure
