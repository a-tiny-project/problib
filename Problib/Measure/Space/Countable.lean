module

public import Problib.Measure.Space

set_option autoImplicit false

/-!
# Countable unions with explicit Nat injections

Supplies countable union measurability for indexed set families whose index type
admits an injection into `Nat`. Empty index types are supported without an
`Inhabited` premise.
-/

namespace Problib.Measure.Space

universe u v

/-- Countable union of measurable sets indexed by a type injecting into `Nat`,
supporting empty index types without an `Inhabited` premise. -/
public theorem i_union_of_nat_injection {ι : Type u} {α : Type v}
    (space : Space α) (code : ι → Nat) (injective : Function.Injective code)
    (sets : ι → Set α) (measurable : ∀ index, space.Measurable (sets index)) :
    space.Measurable (fun value => ∃ index, sets index value) := by
  classical
  let family := fun number value => ∃ index, code index = number ∧ sets index value
  have familyMeasurable : ∀ number, space.Measurable (family number) := by
    intro number
    by_cases represented : ∃ index, code index = number
    · rcases represented with ⟨index, encoded⟩
      have equal : family number = sets index := by
        apply Set.ext
        intro value
        constructor
        · rintro ⟨other, same, member⟩
          have indices : other = index := injective (same.trans encoded.symm)
          exact indices ▸ member
        · intro member
          exact ⟨index, encoded, member⟩
      rw [equal]
      exact measurable index
    · have equal : family number = Set.empty := by
        apply Set.ext
        intro value
        exact ⟨fun ⟨index, encoded, _⟩ => represented ⟨index, encoded⟩, False.elim⟩
      rw [equal]
      exact space.empty
  have equal : (fun value => ∃ index, sets index value) = Set.iUnion family := by
    apply Set.ext
    intro value
    exact ⟨fun ⟨index, member⟩ => ⟨code index, index, rfl, member⟩,
      fun ⟨_, index, _, member⟩ => ⟨index, member⟩⟩
  rw [equal]
  exact space.iUnion familyMeasurable

end Problib.Measure.Space
