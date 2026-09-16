module

public import Foundations.Measure.Space

set_option autoImplicit false

/-!
# Countable generators of measurable spaces

Defines countable generators for measurable spaces and proves measurability of
generating sets and stability under comap pullback.
-/

namespace Foundations.Measure.Space

universe u v

/-- A countable family of sets that generates the σ-algebra of a measurable space. -/
public structure CountableGenerator {α : Type u} (space : Space α) where
  sets : Nat → Set α
  generated : space = Space.generated (fun set => ∃ index, sets index = set)

namespace CountableGenerator

variable {α : Type u} {β : Type v} {space : Space α}

/-- Every set in the countable generator is measurable in the space. -/
public theorem measurable (generator : CountableGenerator space) (index : Nat) :
    space.Measurable (generator.sets index) := by
  apply (congrArg (fun current : Space α => current.Measurable (generator.sets index))
    generator.generated).mpr
  exact Space.generated_contains ⟨index, rfl⟩

/-- Pullback of a countable generator along an arbitrary map to generate the comap space. -/
@[expose] public def comap (generator : CountableGenerator space) (function : β → α) :
    CountableGenerator (Space.comap function space) where
  sets := fun index => Set.preimage function (generator.sets index)
  generated := by
    apply Space.ext
    intro set
    constructor
    · apply Space.comap_minimal
      apply (congrArg (fun target : Space α => MeasurableMap
        (Space.generated (fun region => ∃ index,
          Set.preimage function (generator.sets index) = region)) target function)
          generator.generated).mpr
      apply MeasurableMap.intoGenerated
      rintro region ⟨index, rfl⟩
      exact Space.generated_contains ⟨index, rfl⟩
    · apply Space.generated_minimal
        (Space.comap function space)
      rintro region ⟨index, rfl⟩
      exact Space.comap_map function space (generator.measurable index)

end CountableGenerator

end Foundations.Measure.Space
