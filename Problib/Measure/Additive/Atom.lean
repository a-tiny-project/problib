module
public import Problib.Measure.Additive.Core

set_option autoImplicit false

/-!
# Measures determined by their atoms

On a space with measurable singletons and an injection into the natural
numbers, every measurable set is a countable disjoint union of singletons and
empty pieces, so a measure is fixed by its atoms.
-/

namespace Problib.Measure
open Problib.Real
public section
universe u

namespace Measure

variable {α : Type u} {space : Space α}

/-- Measures on a countable space with measurable singletons agree when their
atoms agree. -/
public theorem ext_of_atoms (code : α → Nat) (injective : Function.Injective code)
    (singletons : ∀ value, space.Measurable (Set.singleton value))
    {left right : Measure space}
    (atoms : ∀ value, left (Set.singleton value) = right (Set.singleton value)) :
    left = right := by
  classical
  apply Measure.ext
  intro set setMeasurable
  let pieces : Nat → Set α := fun index value => set value ∧ code value = index
  have piece : ∀ index, (∃ value, set value ∧ code value = index ∧
      pieces index = Set.singleton value) ∨ pieces index = Set.empty := by
    intro index
    by_cases present : ∃ value, set value ∧ code value = index
    · rcases present with ⟨value, member, coded⟩
      refine Or.inl ⟨value, member, coded, ?_⟩
      apply Set.ext
      intro other
      constructor
      · rintro ⟨_, otherCoded⟩
        exact injective (otherCoded.trans coded.symm)
      · intro same
        change other = value at same
        subst same
        exact ⟨member, coded⟩
    · refine Or.inr (Set.ext fun other => ⟨fun member => present ⟨other, member⟩,
        False.elim⟩)
  have piecesMeasurable : ∀ index, space.Measurable (pieces index) := by
    intro index
    rcases piece index with ⟨value, _, _, equal⟩ | equal
    · rw [equal]
      exact singletons value
    · rw [equal]
      exact space.empty
  have disjoint : Set.PairwiseDisjoint pieces := by
    intro first second different value firstMember secondMember
    exact different (firstMember.2.symm.trans secondMember.2)
  have union : Set.iUnion pieces = set := by
    apply Set.ext
    intro value
    exact ⟨fun ⟨_, member⟩ => member.1, fun member => ⟨code value, member, rfl⟩⟩
  rw [← union, left.iUnion_disjoint pieces piecesMeasurable disjoint,
    right.iUnion_disjoint pieces piecesMeasurable disjoint]
  apply ENNReal.tsum_congr
  intro index
  rcases piece index with ⟨value, _, _, equal⟩ | equal
  · rw [equal]
    exact atoms value
  · rw [equal, left.empty_apply, right.empty_apply]

end Measure
end
end Problib.Measure
