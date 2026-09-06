namespace Foundations.Probability

universe u

structure FiniteSet (α : Type u) [DecidableEq α] where
  elements : List α
  nodup : elements.Nodup
deriving Repr

namespace FiniteSet

variable {α : Type u}

instance [DecidableEq α] : Membership α (FiniteSet α) where
  mem set value := value ∈ set.elements

instance [DecidableEq α] {value : α} {set : FiniteSet α} : Decidable (value ∈ set) := by
  show Decidable (value ∈ set.elements)
  infer_instance

instance [DecidableEq α] : EmptyCollection (FiniteSet α) where
  emptyCollection := ⟨[], .nil⟩

def insert [DecidableEq α] (value : α) (set : FiniteSet α) : FiniteSet α :=
  if present : value ∈ set then
    set
  else
    ⟨value :: set.elements, List.nodup_cons.2 ⟨present, set.nodup⟩⟩

@[simp] theorem mem_empty [DecidableEq α] {value : α} : value ∈ ({} : FiniteSet α) ↔ False := by
  constructor
  · intro member
    change value ∈ ([] : List α) at member
    cases member
  · exact False.elim

@[simp] theorem mem_insert [DecidableEq α] {value inserted : α} {set : FiniteSet α} :
    value ∈ insert inserted set ↔ value = inserted ∨ value ∈ set := by
  by_cases present : inserted ∈ set
  · constructor
    · intro member
      exact Or.inr (by simpa [insert, present] using member)
    · intro member
      cases member with
      | inl equal =>
          subst equal
          simp [insert, present]
      | inr member =>
          simpa [insert, present] using member
  · rw [insert, dif_neg present]
    change value ∈ (inserted :: set.elements) ↔ value = inserted ∨ value ∈ set.elements
    simp

def ofList [DecidableEq α] : List α → FiniteSet α
  | [] => {}
  | value :: rest => insert value (ofList rest)

@[simp] theorem mem_ofList [DecidableEq α] {value : α} {values : List α} :
    value ∈ ofList values ↔ value ∈ values := by
  induction values with
  | nil => simp [ofList]
  | cons head tail ih => simp [ofList, ih]

end FiniteSet

end Foundations.Probability
