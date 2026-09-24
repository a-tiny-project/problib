module

public import Problib.Measure.Additive.Finite
public import Problib.Measure.Additive.AbsoluteContinuity

set_option autoImplicit false

/-!
Residual measures from finite dominated subtrahends.

Domination and global finiteness of the subtrahend construct the unique
additive residual measure. Measurable evaluation agrees with pointwise
difference, and the residual satisfies an order adjunction.
-/

namespace Problib.Measure.Measure

open Problib.Real

universe u v

variable {alpha : Type u} {space : Space alpha}

/-- Construct the residual measure when a globally finite measure lies below
another measure on all measurable sets. -/
@[expose] public noncomputable def subtract {left right : Measure space}
    (rightFinite : IsFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (right set) (left set)) :
    Measure space where
  content := fun set _ => ENNReal.sub (left set) (right set)
  empty := by rw [left.empty_apply, right.empty_apply, ENNReal.sub_self]
  content_iUnion_disjoint := by
    intro sets measurable disjoint
    have finite : ENNReal.Finite (ENNReal.tsum (fun index => right (sets index))) := by
      rw [← right.iUnion_disjoint sets measurable disjoint]
      exact rightFinite.apply _
    rw [left.iUnion_disjoint sets measurable disjoint,
      right.iUnion_disjoint sets measurable disjoint]
    exact (ENNReal.tsum_sub (fun index => included (sets index) (measurable index)) finite).symm

/-- Evaluate the residual measure on a measurable set as the pointwise
difference of minuend and subtrahend masses. -/
public theorem subtract_apply {left right : Measure space}
    (rightFinite : IsFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (right set) (left set))
    {set : Set alpha} (measurable : space.Measurable set) :
    subtract rightFinite included set = ENNReal.sub (left set) (right set) := by
  rw [(subtract rightFinite included).apply_measurable measurable]
  rfl

/-- Reconstruct the minuend measure exactly by adding the finite subtrahend
measure to the residual measure. -/
public theorem subtract_add {left right : Measure space}
    (rightFinite : IsFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (right set) (left set)) :
    Measure.add (subtract rightFinite included) right = left := by
  apply Measure.ext
  intro set measurable
  rw [Measure.add_apply_measurable _ _ measurable, subtract_apply rightFinite included measurable]
  exact ENNReal.sub_add_cancel (included set measurable)

/-- Establish uniqueness of the residual measure by finite additive
cancellation. -/
public theorem subtract_unique {left right remainder : Measure space}
    (rightFinite : IsFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (right set) (left set))
    (reconstruct : Measure.add remainder right = left) :
    remainder = subtract rightFinite included := by
  apply add_right_cancel_of_finite rightFinite
  rw [reconstruct, subtract_add rightFinite included]

/-- Bound the residual measure by the minuend measure on arbitrary sets through
outer-envelope order. -/
public theorem subtract_le {left right : Measure space}
    (rightFinite : IsFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (right set) (left set))
    (set : Set alpha) : ENNReal.le (subtract rightFinite included set) (left set) := by
  apply Measure.le_of_measurable_le _ set
  intro region measurable
  rw [subtract_apply rightFinite included measurable]
  exact ENNReal.sub_le_self _ _

/-- Express the order adjunction between residual bounding and additive
reconstruction over all measurable sets. -/
public theorem le_subtract_iff {left right remainder : Measure space}
    (rightFinite : IsFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (right set) (left set)) :
    (∀ set, space.Measurable set →
      ENNReal.le (remainder set) (subtract rightFinite included set)) ↔
    (∀ set, space.Measurable set → ENNReal.le ((Measure.add remainder right) set) (left set)) := by
  constructor
  · intro bound set measurable
    rw [Measure.add_apply_measurable _ _ measurable]
    apply (ENNReal.le_sub_iff_add_le_of_finite_right (rightFinite.apply set)
      (included set measurable)).mp
    rw [← subtract_apply rightFinite included measurable]
    exact bound set measurable
  · intro bound set measurable
    rw [subtract_apply rightFinite included measurable]
    apply (ENNReal.le_sub_iff_add_le_of_finite_right (rightFinite.apply set)
      (included set measurable)).mpr
    rw [← Measure.add_apply_measurable _ _ measurable]
    exact bound set measurable

/-- Conclude finiteness of the residual measure when the minuend measure is
finite. -/
public theorem IsFinite.subtract {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (right set) (left set)) :
    IsFinite (Measure.subtract rightFinite included) :=
  IsFinite.of_le leftFinite (subtract_le rightFinite included Set.univ)

/-- Relate a vanishing residual measure to exact equality of minuend and
subtrahend measures. -/
public theorem subtract_eq_zero_iff {left right : Measure space}
    (rightFinite : IsFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (right set) (left set)) :
    subtract rightFinite included = Measure.zero space ↔ left = right := by
  constructor
  · intro zero
    have reconstruct := subtract_add rightFinite included
    rw [zero, Measure.zero_add] at reconstruct
    exact reconstruct.symm
  · intro equal
    apply Measure.ext
    intro set measurable
    rw [subtract_apply rightFinite included measurable, equal,
      ENNReal.sub_self, Measure.zero_apply]

/-- Commute measure restriction to a measurable region with residual
subtraction. -/
public theorem restrict_subtract {left right : Measure space}
    (rightFinite : IsFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (right set) (left set))
    {region : Set alpha} (regionMeasurable : space.Measurable region) :
    (subtract rightFinite included).restrict region =
      subtract (rightFinite.restrict region)
        (fun set _ => restrict_le_restrict included region set) := by
  apply subtract_unique
  rw [← restrict_add _ _ regionMeasurable, subtract_add]

/-- Commute pushforward along a measurable map with residual subtraction. -/
public theorem map_subtract {beta : Type v} {target : Space beta}
    {left right : Measure space} (rightFinite : IsFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (right set) (left set))
    (function : alpha → beta) (measurable : MeasurableMap space target function) :
    (subtract rightFinite included).map function measurable =
      subtract (rightFinite.map function measurable)
        (fun set _ => map_le_map included function measurable set) := by
  apply subtract_unique
  rw [← map_add, subtract_add]

end Problib.Measure.Measure
