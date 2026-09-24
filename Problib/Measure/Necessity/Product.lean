module

public import Problib.Measure.Space

set_option autoImplicit false

namespace Problib.Measure.Necessity

open Problib.Measure

universe u v

variable {α : Type u} {β : Type v}

public section

def FirstDetermined (set : Set (α × β)) : Prop :=
  ∀ left right, left.1 = right.1 → (set left ↔ set right)

theorem left_comap_is_firstDetermined (left : Space α) {set : Set (α × β)}
    (measurable : (Space.comap Prod.fst left).Measurable set) :
    FirstDetermined set := by
  induction measurable with
  | basic generator =>
      rcases generator with ⟨targetSet, targetMeasurable, rfl⟩
      intro first second equal
      change targetSet first.1 ↔ targetSet second.1
      rw [equal]
  | empty =>
      intro first second equal
      exact Iff.rfl
  | complement setMeasurable induction =>
      intro first second equal
      exact not_congr (induction first second equal)
  | iUnion setsMeasurable induction =>
      intro first second equal
      constructor
      · rintro ⟨index, member⟩
        exact ⟨index, (induction index first second equal).mp member⟩
      · rintro ⟨index, member⟩
        exact ⟨index, (induction index first second equal).mpr member⟩

def trueOnly : Set Bool :=
  Set.singleton true

theorem missing_right_generators_break_second_projection :
    ¬MeasurableMap
      (Space.comap Prod.fst (Space.discrete Bool))
      (Space.discrete Bool)
      Prod.snd := by
  intro secondMeasurable
  have preimageMeasurable := secondMeasurable
    (set := trueOnly) True.intro
  have determined := left_comap_is_firstDetermined
    (β := Bool) (Space.discrete Bool) preimageMeasurable
  have same := determined (false, true) (false, false) rfl
  have trueMember : Set.preimage Prod.snd trueOnly (false, true) := rfl
  have falseMember := same.mp trueMember
  exact Bool.noConfusion falseMember

end

end Problib.Measure.Necessity
