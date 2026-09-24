module

public import Problib.Measure.Space.Generator
import Problib.Countable.Bijection

set_option autoImplicit false

/-!
# Countable generating algebras for measurable spaces

Defines countable algebras extending countable generators with closure under
empty, complement, and binary union. Constructs the generated countable algebra
from any countable generator through ternary term encoding.
-/

namespace Problib.Measure.Space

universe u

/-- A countable family of sets forming an algebra (closed under empty, complement,
and binary union) that generates the σ-algebra of a measurable space. -/
public structure CountableAlgebra {α : Type u} (space : Space α)
    extends CountableGenerator space where
  empty : ∃ index, sets index = Set.empty
  complement : ∀ index, ∃ other, sets other = Set.complement (sets index)
  union : ∀ left right, ∃ index, sets index = Set.union (sets left) (sets right)

namespace CountableGenerator

variable {α : Type u} {space : Space α}

private def algebraSets (generators : Nat → Set α) : Nat → Set α
  | 0 => Set.empty
  | index + 1 =>
      if index % 3 = 0 then generators (index / 3)
      else if index % 3 = 1 then Set.complement (algebraSets generators (index / 3))
      else Set.union
        (algebraSets generators (Countable.Pair.decode (index / 3)).1)
        (algebraSets generators (Countable.Pair.decode (index / 3)).2)
termination_by index => index
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.div_le_self _ _)
  · exact Nat.lt_succ_of_le
      (Nat.le_trans (Countable.Pair.decode_first_le _) (Nat.div_le_self _ _))
  · exact Nat.lt_succ_of_le
      (Nat.le_trans (Countable.Pair.decode_second_le _) (Nat.div_le_self _ _))

private theorem algebraSets_generator (generators : Nat → Set α) (index : Nat) :
    algebraSets generators (3 * index + 1) = generators index := by
  rw [algebraSets]
  simp

private theorem algebraSets_complement (generators : Nat → Set α) (index : Nat) :
    algebraSets generators (3 * index + 2) =
      Set.complement (algebraSets generators index) := by
  rw [show 3 * index + 2 = (3 * index + 1) + 1 by omega, algebraSets]
  have remainder : (3 * index + 1) % 3 = 1 := by omega
  have quotient : (3 * index + 1) / 3 = index := by omega
  simp only [remainder, Nat.one_ne_zero, if_false, if_true, quotient]

private theorem algebraSets_union (generators : Nat → Set α) (left right : Nat) :
    algebraSets generators (3 * Countable.Pair.encode (left, right) + 3) =
      Set.union (algebraSets generators left) (algebraSets generators right) := by
  let code := Countable.Pair.encode (left, right)
  rw [show 3 * Countable.Pair.encode (left, right) + 3 = (3 * code + 2) + 1 by omega,
    algebraSets]
  have remainder : (3 * code + 2) % 3 = 2 := by omega
  have quotient : (3 * code + 2) / 3 = code := by omega
  rw [remainder, if_neg (by decide : ¬(2 : Nat) = 0),
    if_neg (by decide : ¬(2 : Nat) = 1), quotient]
  change Set.union
      (algebraSets generators (Countable.Pair.decode (Countable.Pair.encode (left, right))).1)
      (algebraSets generators (Countable.Pair.decode (Countable.Pair.encode (left, right))).2) = _
  rw [Countable.Pair.decode_encode]

private theorem algebraSets_measurable (generators : Nat → Set α)
    (measurable : ∀ index, space.Measurable (generators index)) (index : Nat) :
    space.Measurable (algebraSets generators index) := by
  induction index using Nat.strongRecOn with
  | ind index induction =>
      cases index with
      | zero => simpa only [algebraSets] using space.empty
      | succ index =>
          rw [algebraSets]
          by_cases generator : index % 3 = 0
          · rw [if_pos generator]
            exact measurable _
          · rw [if_neg generator]
            by_cases complement : index % 3 = 1
            · rw [if_pos complement]
              exact space.complement
                (induction _ (Nat.lt_succ_of_le (Nat.div_le_self _ _)))
            · rw [if_neg complement]
              exact space.union
                (induction _ (Nat.lt_succ_of_le (Nat.le_trans
                  (Countable.Pair.decode_first_le _) (Nat.div_le_self _ _))))
                (induction _ (Nat.lt_succ_of_le (Nat.le_trans
                  (Countable.Pair.decode_second_le _) (Nat.div_le_self _ _))))
/-- Constructs a countable generating algebra from any countable generator by freely
closing under empty, complement, and binary union using natural pairing. -/
public def algebra (generator : CountableGenerator space) : CountableAlgebra space where
  sets := algebraSets generator.sets
  generated := by
    apply Space.ext
    intro set
    constructor
    · intro measurable
      have generatedMeasurable := (congrArg
        (fun current : Space α => current.Measurable set) generator.generated).mp measurable
      refine Space.generated_minimal _ ?_ generatedMeasurable
      rintro region ⟨index, rfl⟩
      rw [← algebraSets_generator generator.sets index]
      exact Space.generated_contains ⟨3 * index + 1, rfl⟩
    · apply Space.generated_minimal space
      rintro region ⟨index, rfl⟩
      exact algebraSets_measurable generator.sets generator.measurable index
  empty := ⟨0, by rw [algebraSets]⟩
  complement := fun index => ⟨3 * index + 2, algebraSets_complement generator.sets index⟩
  union := fun left right => ⟨3 * Countable.Pair.encode (left, right) + 3,
    algebraSets_union generator.sets left right⟩

end CountableGenerator

end Problib.Measure.Space
