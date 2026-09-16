module

public import Foundations.Measure.Set

set_option autoImplicit false

/-!
# Symmetric difference of sets

Defines the symmetric difference operation on sets and proves algebraic properties
including self-annihilation, symmetry, triangle inclusion, and union subadditivity.
-/

namespace Foundations.Measure.Set

universe u

variable {α : Type u}

/-- Symmetric difference of two sets, $(A \setminus B) \cup (B \setminus A)$. -/
@[expose] public def symmDiff (left right : Set α) : Set α :=
  union (difference left right) (difference right left)

/-- Symmetric difference of a set with itself is empty. -/
public theorem symmDiff_self (set : Set α) : symmDiff set set = empty := by
  apply ext
  intro value
  simp [symmDiff, union, difference, inter, complement, empty]

/-- Symmetric difference is commutative. -/
public theorem symmDiff_comm (left right : Set α) : symmDiff left right = symmDiff right left := by
  apply ext
  intro value
  exact or_comm

/-- Complementation preserves symmetric difference. -/
public theorem symmDiff_complement (left right : Set α) :
    symmDiff (complement left) (complement right) = symmDiff left right := by
  classical
  apply ext
  intro value
  by_cases first : left value <;> by_cases second : right value <;>
    simp [symmDiff, union, difference, inter, complement, first, second]

/-- Triangle inclusion for symmetric differences. -/
public theorem symmDiff_triangle (first middle last : Set α) :
    Subset (symmDiff first last) (union (symmDiff first middle) (symmDiff middle last)) := by
  classical
  intro value member
  by_cases firstMember : first value <;> by_cases middleMember : middle value <;>
    by_cases lastMember : last value <;>
      simp_all [symmDiff, union, difference, inter, complement]

/-- Subadditivity of symmetric difference across binary unions. -/
public theorem symmDiff_union (first second left right : Set α) :
    Subset (symmDiff (union first second) (union left right))
      (union (symmDiff first left) (symmDiff second right)) := by
  classical
  intro value member
  by_cases firstMember : first value <;> by_cases secondMember : second value <;>
    by_cases leftMember : left value <;> by_cases rightMember : right value <;>
      simp_all [symmDiff, union, difference, inter, complement]

/-- When one set contains another, their symmetric difference reduces to set difference. -/
public theorem symmDiff_of_subset {left right : Set α} (included : Subset right left) :
    symmDiff left right = difference left right := by
  apply ext
  intro value
  constructor
  · rintro (member | member)
    · exact member
    · exact False.elim (member.2 (included member.1))
  · exact Or.inl

/-- Every set is covered by any other set and their symmetric difference. -/
public theorem subset_union_symmDiff (left right : Set α) :
    Subset left (union right (symmDiff left right)) := by
  classical
  intro value member
  by_cases present : right value
  · exact Or.inl present
  · exact Or.inr (Or.inl ⟨member, present⟩)

end Foundations.Measure.Set
