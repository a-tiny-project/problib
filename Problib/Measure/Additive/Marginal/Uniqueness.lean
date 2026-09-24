module

public import Problib.Measure.Additive.Marginal
public import Problib.Measure.Additive.Continuity
public import Problib.Measure.Dynkin.Uniqueness
public import Problib.Measure.Product.Generator

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}

/-- Two joint measures agree when the right measure has a sigma-finite second
marginal and evaluations agree on measurable rectangles where the right
second marginal is finite. -/
public theorem ext_of_secondMarginal
    {left right : Measure (Space.product source target)}
    (finite : SigmaFinite (secondMarginal right))
    (rectangles : ∀ first second, source.Measurable first → target.Measurable second →
      ENNReal.Finite (secondMarginal right second) →
        left (Set.product first second) = right (Set.product first second)) : left = right := by
  let span : Nat → Set (alpha × beta) := fun index => Set.preimage Prod.snd (finite.sets index)
  have spanMeasurable : ∀ index, (Space.product source target).Measurable (span index) :=
    fun index => Space.second_measurable source target (finite.measurable index)
  have spanRightFinite (index : Nat) : ENNReal.Finite (right (span index)) := by
    rw [← secondMarginal_apply right (finite.measurable index)]
    exact finite.finite index
  have spanEqual (index : Nat) : left (span index) = right (span index) := by
    have same : span index = Set.product (Set.univ : Set alpha) (finite.sets index) := by
      apply Set.ext
      intro value
      exact ⟨fun member => ⟨True.intro, member⟩, fun member => member.2⟩
    rw [same]
    exact rectangles Set.univ (finite.sets index) source.univ
      (finite.measurable index) (finite.finite index)
  have restrictedEqual (index : Nat) : left.restrict (span index) = right.restrict (span index) := by
    have leftFinite : IsFinite (left.restrict (span index)) := by
      constructor
      rw [restrict_apply_univ, spanEqual index]
      exact spanRightFinite index
    have rightFinite : IsFinite (right.restrict (span index)) := by
      constructor
      rw [restrict_apply_univ]
      exact spanRightFinite index
    apply ext_of_generate (Space.Rectangle source target)
      (Space.product_eq_generated_rectangles source target)
      (Space.rectangle_piSystem source target) (Space.rectangle_contains_univ source target)
      leftFinite rightFinite
    rintro rectangle ⟨first, second, firstMeasurable, secondMeasurable, rfl⟩
    rw [left.restrict_apply _
      (Space.product_set_measurable source target firstMeasurable secondMeasurable),
      right.restrict_apply _
        (Space.product_set_measurable source target firstMeasurable secondMeasurable)]
    have same : Set.inter (Set.product first second) (span index) =
        Set.product first (Set.inter second (finite.sets index)) := by
      apply Set.ext
      intro value
      exact ⟨fun member => ⟨member.1.1, member.1.2, member.2⟩,
        fun member => ⟨⟨member.1, member.2.1⟩, member.2.2⟩⟩
    rw [same]
    exact rectangles first _ firstMeasurable
      (target.inter secondMeasurable (finite.measurable index))
      (ENNReal.finite_of_le ((secondMarginal right).mono (fun _ member => member.2))
        (finite.finite index))
  apply Measure.ext
  intro set measurable
  let slices := fun index => Set.inter set (span index)
  have slicesMeasurable : ∀ index, (Space.product source target).Measurable (slices index) :=
    fun index => (Space.product source target).inter measurable (spanMeasurable index)
  have slicesMonotone : Set.MonotoneFamily slices :=
    fun {_ _} included {_} member => ⟨member.1, finite.monotone included member.2⟩
  have slicesUnion : Set.iUnion slices = set := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨index, member⟩
      exact member.1
    · intro member
      have covered : Set.iUnion finite.sets value.2 := by
        rw [finite.cover]
        exact True.intro
      rcases covered with ⟨index, present⟩
      exact ⟨index, member, present⟩
  have sliceEqual (index : Nat) : left (slices index) = right (slices index) := by
    have equal := congrArg (fun measure => measure set) (restrictedEqual index)
    simpa only [restrict_apply _ _ measurable] using equal
  calc
    left set = ENNReal.iSup (fun index => left (slices index)) := by
      rw [← left.continuity_from_below slices slicesMeasurable slicesMonotone, slicesUnion]
    _ = ENNReal.iSup (fun index => right (slices index)) := by
      apply congrArg ENNReal.iSup
      funext index
      exact sliceEqual index
    _ = right set := by
      rw [← right.continuity_from_below slices slicesMeasurable slicesMonotone, slicesUnion]

end Problib.Measure.Measure
