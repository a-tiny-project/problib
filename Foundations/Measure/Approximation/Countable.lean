module

public import Foundations.Measure.Approximation.Basic
public import Foundations.Measure.Additive.Finite
import Foundations.Measure.Additive.Continuity
import Foundations.Real.Nonnegative.Dyadic

set_option autoImplicit false

/-!
# Approximation of measurable sets by countable generating algebras

Proves that under any finite measure, every measurable set in a countably
generated space is approximable by the countable generating algebra.
Countable union closure holds through continuity from above on decreasing tails.
-/

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {α : Type u} {space : Space α} {measure : Measure space}

namespace Approximable

/-- Countable unions of approximable sets are approximable under any finite measure. -/
public theorem iUnion (finite : IsFinite measure) (algebra : Space.CountableAlgebra space)
    (sets : Nat → Set α) (measurable : ∀ index, space.Measurable (sets index))
    (approximation : ∀ index, measure.Approximable algebra.sets (sets index)) :
    measure.Approximable algebra.sets (Set.iUnion sets) := by
  intro epsilon positive
  let tails : Nat → Set α :=
    fun index => Set.difference (Set.iUnion sets) (Set.prefixUnion sets index)
  have tailsMeasurable : ∀ index, space.Measurable (tails index) :=
    fun index => space.difference (space.iUnion measurable)
      (space.prefixUnion_measurable measurable index)
  have tailsAntitone : Set.AntitoneFamily tails := by
    intro first second included value member
    exact ⟨member.1, fun earlier => member.2 (Set.prefixUnion_monotone sets included earlier)⟩
  have tailsEmpty : Set.iInter tails = Set.empty := by
    apply Set.ext
    intro value
    constructor
    · intro member
      rcases (member 0).1 with ⟨index, included⟩
      exact (member (index + 1)).2 (Set.subset_prefixUnion_succ sets index included)
    · exact False.elim
  have continuous := measure.continuity_from_above tails tailsMeasurable tailsAntitone
    (finite.apply (tails 0))
  have halfPositive := NNReal.halfPositive positive
  have infimumLess : ENNReal.lt (ENNReal.iInf (fun index => measure (tails index)))
      (ENNReal.finite (NNReal.half epsilon)) := by
    rw [← continuous, tailsEmpty, measure.empty_apply]
    exact halfPositive
  rcases ENNReal.existsIndexLessOfIInfLt infimumLess with ⟨count, tailLess⟩
  rcases (prefixUnion sets approximation count) (NNReal.half epsilon) halfPositive with
    ⟨index, prefixBound⟩
  refine ⟨index, ?_⟩
  have tailBound : ENNReal.le
      (measure.setDistance (Set.iUnion sets) (Set.prefixUnion sets count))
      (ENNReal.finite (NNReal.half epsilon)) := by
    rw [setDistance, Set.symmDiff_of_subset (Set.prefixUnion_subset_iUnion sets count)]
    exact tailLess.1
  have bound := ENNReal.leTrans (measure.setDistance_triangle (Set.iUnion sets)
    (Set.prefixUnion sets count) (algebra.sets index))
    (ENNReal.addLeAdd tailBound prefixBound)
  have halves : ENNReal.add (ENNReal.finite (NNReal.half epsilon))
      (ENNReal.finite (NNReal.half epsilon)) = ENNReal.finite epsilon :=
    congrArg ENNReal.finite (NNReal.halfAddHalf epsilon)
  rw [halves] at bound
  exact bound

end Approximable

/-- Under any finite measure, every measurable set in a countably generated space
is approximable in measure distance by elements of the generating algebra. -/
public theorem approximable_of_measurable (finite : IsFinite measure)
    (algebra : Space.CountableAlgebra space) {region : Set α}
    (measurable : space.Measurable region) : measure.Approximable algebra.sets region := by
  let approximationSpace : Space α := {
    Measurable := fun set => space.Measurable set ∧ measure.Approximable algebra.sets set
    empty := ⟨space.empty, Approximable.empty⟩
    complement := fun included => ⟨space.complement included.1, included.2.complement⟩
    iUnion := fun included => ⟨space.iUnion (fun index => (included index).1),
      Approximable.iUnion finite algebra _ (fun index => (included index).1)
        (fun index => (included index).2)⟩ }
  have generatedMeasurable := (congrArg (fun current : Space α => current.Measurable region)
    algebra.generated).mp measurable
  have contained : ∀ {set : Set α}, (∃ index, algebra.sets index = set) →
      approximationSpace.Measurable set := by
    rintro set ⟨index, rfl⟩
    exact ⟨algebra.toCountableGenerator.measurable index, Approximable.member algebra.sets index⟩
  exact (Space.generated_minimal approximationSpace contained generatedMeasurable).2

end Foundations.Measure.Measure
