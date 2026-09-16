module

public import Foundations.Measure.Space

set_option autoImplicit false

/-!
# Direct sums of measurable spaces

This module constructs the direct sum of two measurable spaces.
A set is measurable if and only if both branch preimages are measurable.
It also proves measurability of injections, elimination, and sum maps.
-/
namespace Foundations.Measure

public section

universe u v w x y z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

namespace Space

/-- Direct sum of two measurable spaces on `Sum α β`.
A region is measurable if and only if its preimage under each injection is measurable. -/
@[expose] def sum (left : Space α) (right : Space β) : Space (Sum α β) where
  Measurable := fun region =>
    left.Measurable (Set.preimage Sum.inl region) ∧
      right.Measurable (Set.preimage Sum.inr region)
  empty := ⟨left.empty, right.empty⟩
  complement := fun measurable =>
    ⟨left.complement measurable.1, right.complement measurable.2⟩
  iUnion := fun measurable =>
    ⟨left.iUnion (fun index => (measurable index).1),
      right.iUnion (fun index => (measurable index).2)⟩

@[simp] theorem sum_measurable_iff (left : Space α) (right : Space β)
    (region : Set (Sum α β)) :
    (sum left right).Measurable region ↔
      left.Measurable (Set.preimage Sum.inl region) ∧
        right.Measurable (Set.preimage Sum.inr region) := Iff.rfl

end Space

namespace MeasurableMap

/-- Proves the canonical left injection `Sum.inl` is a measurable map. -/
theorem inl (left : Space α) (right : Space β) :
    MeasurableMap left (Space.sum left right) Sum.inl :=
  fun measurable => measurable.1

/-- Proves the canonical right injection `Sum.inr` is a measurable map. -/
theorem inr (left : Space α) (right : Space β) :
    MeasurableMap right (Space.sum left right) Sum.inr :=
  fun measurable => measurable.2

/-- Characterizes measurable maps from a sum space.
A function is measurable if and only if its restriction to each summand is measurable. -/
theorem fromSum_iff {left : Space α} {right : Space β} {target : Space γ}
    {function : Sum α β → γ} :
    MeasurableMap (Space.sum left right) target function ↔
      MeasurableMap left target (fun value => function (Sum.inl value)) ∧
        MeasurableMap right target (fun value => function (Sum.inr value)) := by
  constructor
  · intro measurable
    exact ⟨comp measurable (inl left right), comp measurable (inr left right)⟩
  · rintro ⟨leftMeasurable, rightMeasurable⟩ region measurable
    exact ⟨leftMeasurable measurable, rightMeasurable measurable⟩

/-- Eliminates from a sum space by cases.
The resulting map is measurable when both branch maps are measurable. -/
theorem sumElim {left : Space α} {right : Space β} {target : Space γ}
    {leftMap : α → γ} {rightMap : β → γ}
    (leftMeasurable : MeasurableMap left target leftMap)
    (rightMeasurable : MeasurableMap right target rightMap) :
    MeasurableMap (Space.sum left right) target (Sum.elim leftMap rightMap) :=
  fromSum_iff.mpr ⟨leftMeasurable, rightMeasurable⟩

/-- Proves that case elimination is measurable if and only if both branch maps are measurable. -/
theorem sumElim_iff {left : Space α} {right : Space β} {target : Space γ}
    {leftMap : α → γ} {rightMap : β → γ} :
    MeasurableMap (Space.sum left right) target (Sum.elim leftMap rightMap) ↔
      MeasurableMap left target leftMap ∧ MeasurableMap right target rightMap :=
  fromSum_iff

/-- Functorial sum map applying `leftMap` on `α` and `rightMap` on `β`.
The composite map is measurable when both component maps are measurable. -/
theorem sumMap {first : Space α} {second : Space β} {third : Space γ} {fourth : Space δ}
    {leftMap : α → γ} {rightMap : β → δ}
    (leftMeasurable : MeasurableMap first third leftMap)
    (rightMeasurable : MeasurableMap second fourth rightMap) :
    MeasurableMap (Space.sum first second) (Space.sum third fourth)
      (Sum.map leftMap rightMap) :=
  sumElim (comp (inl third fourth) leftMeasurable)
    (comp (inr third fourth) rightMeasurable)

end MeasurableMap

end

end Foundations.Measure
