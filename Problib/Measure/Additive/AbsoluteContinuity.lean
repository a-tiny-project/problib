module

public import Problib.Measure.AlmostEverywhere.Basic
public import Problib.Measure.Additive.Restrict
public import Problib.Measure.Additive.Map

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u v

variable {alpha : Type u} {beta : Sort v} {space : Space alpha}

/-- The target measure vanishes on every measurable reference-null set. -/
@[expose] public def AbsolutelyContinuous
    (target reference : Measure space) : Prop :=
  ∀ {set : Set alpha}, space.Measurable set →
    reference set = ENNReal.zero →
    target set = ENNReal.zero

public theorem AbsolutelyContinuous.refl (measure : Measure space) :
    AbsolutelyContinuous measure measure := by
  intro set measurable zero
  exact zero

public theorem AbsolutelyContinuous.trans
    {target middle reference : Measure space}
    (targetMiddle : AbsolutelyContinuous target middle)
    (middleReference : AbsolutelyContinuous middle reference) :
    AbsolutelyContinuous target reference := by
  intro set measurable referenceZero
  exact targetMiddle measurable
    (middleReference measurable referenceZero)

/-- Transport absolute continuity to a smaller measure dominated on all
measurable sets. -/
public theorem AbsolutelyContinuous.of_le
    {target middle reference : Measure space}
    (continuous : AbsolutelyContinuous middle reference)
    (included : ∀ set, space.Measurable set → ENNReal.le (target set) (middle set)) :
    AbsolutelyContinuous target reference := by
  intro set measurable referenceZero
  have bound := included set measurable
  rw [continuous measurable referenceZero] at bound
  exact ENNReal.eq_zero_of_le_zero bound

/-- Absolute continuity transports vanishing on measurable sets to all arbitrary
outer-null sets through measurable envelopes. -/
public theorem AbsolutelyContinuous.null
    {target reference : Measure space}
    (continuous : AbsolutelyContinuous target reference)
    {set : Set alpha} (nullSet : reference.NullSet set) :
    target.NullSet set := by
  rcases nullSet.exists_measurable_superset with
    ⟨superset, measurable, included, nullSuperset⟩
  exact NullSet.mono (continuous measurable nullSuperset) included

/-- Absolute continuity transports to restrictions on any region, without
requiring region measurability. -/
public theorem AbsolutelyContinuous.restrict
    {target reference : Measure space} (continuous : AbsolutelyContinuous target reference)
    (region : Set alpha) : AbsolutelyContinuous (target.restrict region) (reference.restrict region) := by
  intro set measurable zero
  rw [reference.restrict_apply region measurable] at zero
  rw [target.restrict_apply region measurable]
  exact continuous.null zero

/-- Absolute continuity transports almost-everywhere predicates from reference
to target. -/
public theorem AbsolutelyContinuous.ae
    {target reference : Measure space}
    (continuous : AbsolutelyContinuous target reference)
    {predicate : alpha → Prop} (holds : reference.AE predicate) :
    target.AE predicate :=
  continuous.null holds

public theorem AbsolutelyContinuous.aeEq
    {target reference : Measure space}
    (continuous : AbsolutelyContinuous target reference)
    {left right : alpha → beta} (equal : reference.AEEq left right) :
    target.AEEq left right :=
  continuous.ae equal

/-- Pushforward along a measurable map preserves absolute continuity. -/
public theorem AbsolutelyContinuous.map {gamma : Type v} {ambient : Space gamma} {left right : Measure space}
    (continuous : Measure.AbsolutelyContinuous left right)
    (function : alpha → gamma) (measurable : MeasurableMap space ambient function) :
    Measure.AbsolutelyContinuous (left.map function measurable) (right.map function measurable) := by
  intro set setMeasurable nullSet
  rw [Measure.map_apply _ _ _ setMeasurable] at nullSet ⊢
  exact continuous (measurable setMeasurable) nullSet

end Problib.Measure.Measure
