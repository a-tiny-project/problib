module

public import Problib.Measure.Space

set_option autoImplicit false

/-!
# Countable measurable selection

Proves that any countable measurable cover of a measurable space admits a measurable
selection into the discrete index space, constructed by disjointification.
-/

namespace Problib.Measure.Space

universe u

/-- Given a countable family of measurable sets that covers a space, constructs a
measurable index selection map by disjointifying the sequence. -/
public theorem exists_measurable_selection {α : Type u} (space : Space α)
    (sets : Nat → Set α) (measurable : ∀ index, space.Measurable (sets index))
    (cover : ∀ input, ∃ index, sets index input) :
    ∃ selection : α → Nat, MeasurableMap space (Space.discrete Nat) selection ∧
      ∀ input, sets (selection input) input := by
  classical
  have covered : ∀ input, ∃ index, Set.disjointed sets index input := by
    intro input
    change Set.iUnion (Set.disjointed sets) input
    rw [Set.iUnion_disjointed]
    exact cover input
  let selection : α → Nat := fun input => Classical.choose (covered input)
  have selected : ∀ input, Set.disjointed sets (selection input) input :=
    fun input => Classical.choose_spec (covered input)
  have characterized (input : α) (index : Nat) :
      selection input = index ↔ Set.disjointed sets index input := by
    constructor
    · intro equal
      rw [← equal]
      exact selected input
    · intro included
      apply Classical.byContradiction
      intro different
      exact Set.disjointed_pairwise sets (selection input) index different (selected input) included
  refine ⟨selection, ?_, fun input => (selected input).1⟩
  intro region _
  let pieces : Nat → Set α := fun index =>
    if region index then Set.disjointed sets index else Set.empty
  have equal : Set.preimage selection region = Set.iUnion pieces := by
    apply Set.ext
    intro input
    constructor
    · intro included
      change region (selection input) at included
      refine ⟨selection input, ?_⟩
      simpa only [pieces, if_pos included] using selected input
    · rintro ⟨index, included⟩
      by_cases member : region index
      · simp only [pieces, if_pos member] at included
        change region (selection input)
        rw [(characterized input index).mpr included]
        exact member
      · simp only [pieces, if_neg member] at included
        exact False.elim included
  rw [equal]
  apply space.iUnion
  intro index
  by_cases member : region index
  · simp only [pieces, if_pos member]
    exact space.disjointed_measurable measurable index
  · simp only [pieces, if_neg member]
    exact space.empty

end Problib.Measure.Space
