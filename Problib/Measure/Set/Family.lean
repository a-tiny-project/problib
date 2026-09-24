module

public import Problib.Measure.Set

namespace Problib.Measure

universe u

variable {α : Type u}

set_option autoImplicit false

public section

namespace Set

@[expose] def prefixUnion (sets : Nat → Set α) : Nat → Set α
  | 0 => empty
  | index + 1 => union (prefixUnion sets index) (sets index)

@[simp] theorem prefixUnion_zero (sets : Nat → Set α) :
    prefixUnion sets 0 = empty :=
  rfl

@[simp] theorem prefixUnion_succ (sets : Nat → Set α) (index : Nat) :
    prefixUnion sets (index + 1) =
      union (prefixUnion sets index) (sets index) :=
  rfl

theorem mem_prefixUnion_iff (sets : Nat → Set α) (bound : Nat) (value : α) :
    value ∈ prefixUnion sets bound ↔
      ∃ index, index < bound ∧ value ∈ sets index := by
  induction bound with
  | zero =>
      constructor
      · intro member
        exact False.elim member
      · rintro ⟨index, less, _⟩
        exact False.elim (Nat.not_lt_zero index less)
  | succ bound induction =>
      constructor
      · intro member
        cases member with
        | inl earlier =>
            rcases induction.mp earlier with ⟨index, less, indexMember⟩
            exact ⟨index, Nat.lt_trans less (Nat.lt_succ_self bound), indexMember⟩
        | inr latest => exact ⟨bound, Nat.lt_succ_self bound, latest⟩
      · rintro ⟨index, less, indexMember⟩
        have atMost : index ≤ bound := Nat.le_of_lt_succ less
        cases Nat.lt_or_eq_of_le atMost with
        | inl earlier => exact Or.inl (induction.mpr ⟨index, earlier, indexMember⟩)
        | inr latest =>
            subst index
            exact Or.inr indexMember

theorem subset_prefixUnion_of_lt (sets : Nat → Set α) {index bound : Nat}
    (less : index < bound) : Subset (sets index) (prefixUnion sets bound) := by
  intro value member
  exact (mem_prefixUnion_iff sets bound value).mpr ⟨index, less, member⟩

theorem subset_prefixUnion_succ (sets : Nat → Set α) (index : Nat) :
    Subset (sets index) (prefixUnion sets (index + 1)) :=
  subset_prefixUnion_of_lt sets (Nat.lt_succ_self index)

theorem prefixUnion_subset_iUnion (sets : Nat → Set α) (bound : Nat) :
    Subset (prefixUnion sets bound) (iUnion sets) := by
  intro value member
  rcases (mem_prefixUnion_iff sets bound value).mp member with
    ⟨index, _, indexMember⟩
  exact ⟨index, indexMember⟩

theorem prefixUnion_monotone (sets : Nat → Set α) :
    MonotoneFamily (prefixUnion sets) := by
  intro first second firstSecond value member
  rcases (mem_prefixUnion_iff sets first value).mp member with
    ⟨index, less, indexMember⟩
  exact (mem_prefixUnion_iff sets second value).mpr
    ⟨index, Nat.lt_of_lt_of_le less firstSecond, indexMember⟩

theorem iUnion_prefixUnion (sets : Nat → Set α) :
    iUnion (prefixUnion sets) = iUnion sets := by
  apply ext
  intro value
  constructor
  · rintro ⟨bound, member⟩
    exact prefixUnion_subset_iUnion sets bound member
  · rintro ⟨index, member⟩
    exact ⟨index + 1, subset_prefixUnion_succ sets index member⟩

theorem prefixUnion_succ_eq_of_monotone {sets : Nat → Set α}
    (monotone : MonotoneFamily sets) (index : Nat) :
    prefixUnion sets (index + 1) = sets index := by
  apply subset_antisymm
  · intro value member
    rcases (mem_prefixUnion_iff sets (index + 1) value).mp member with
      ⟨earlier, less, earlierMember⟩
    exact monotone (Nat.le_of_lt_succ less) earlierMember
  · exact subset_prefixUnion_succ sets index

@[expose] def disjointed (sets : Nat → Set α) (index : Nat) : Set α :=
  difference (sets index) (prefixUnion sets index)

theorem disjointed_subset (sets : Nat → Set α) (index : Nat) :
    Subset (disjointed sets index) (sets index) :=
  difference_subset (sets index) (prefixUnion sets index)

theorem prefixUnion_disjoint_right {sets : Nat → Set α}
    (pairwise : PairwiseDisjoint sets) (index : Nat) :
    Disjoint (prefixUnion sets index) (sets index) := by
  intro value prefixMember indexMember
  rcases (mem_prefixUnion_iff sets index value).mp prefixMember with
    ⟨earlier, less, earlierMember⟩
  exact pairwise earlier index (Nat.ne_of_lt less) earlierMember indexMember

theorem disjointed_pairwise (sets : Nat → Set α) :
    PairwiseDisjoint (disjointed sets) := by
  intro first second different
  cases Nat.lt_or_gt_of_ne different with
  | inl firstSecond =>
      intro value firstMember secondMember
      exact secondMember.2
        (subset_prefixUnion_of_lt sets firstSecond firstMember.1)
  | inr secondFirst =>
      intro value firstMember secondMember
      exact firstMember.2
        (subset_prefixUnion_of_lt sets secondFirst secondMember.1)

theorem prefixUnion_disjointed (sets : Nat → Set α) (bound : Nat) :
    prefixUnion (disjointed sets) bound = prefixUnion sets bound := by
  induction bound with
  | zero => rfl
  | succ bound induction =>
      change union (prefixUnion (disjointed sets) bound)
          (difference (sets bound) (prefixUnion sets bound)) =
        union (prefixUnion sets bound) (sets bound)
      rw [induction]
      exact union_difference_absorb (prefixUnion sets bound) (sets bound)

theorem iUnion_disjointed (sets : Nat → Set α) :
    iUnion (disjointed sets) = iUnion sets := by
  calc
    iUnion (disjointed sets) = iUnion (prefixUnion (disjointed sets)) :=
      (iUnion_prefixUnion (disjointed sets)).symm
    _ = iUnion (prefixUnion sets) := by
      apply congrArg iUnion
      apply funext
      exact prefixUnion_disjointed sets
    _ = iUnion sets := iUnion_prefixUnion sets

/-- The finite prefix intersection of a sequence of sets.
The prefix intersection of zero sets is the entire universe. -/
@[expose] def prefixInter (sets : Nat → Set α) : Nat → Set α
  | 0 => univ
  | count + 1 => inter (prefixInter sets count) (sets count)

theorem mem_prefixInter (sets : Nat → Set α) (count : Nat) (value : α) :
    prefixInter sets count value ↔ ∀ index, index < count → sets index value := by
  induction count with
  | zero =>
      exact ⟨fun _ index impossible => False.elim (by omega), fun _ => True.intro⟩
  | succ count induction =>
      constructor
      · intro member index included
        by_cases last : index = count
        · exact last ▸ member.2
        · exact induction.mp member.1 index (by omega)
      · intro member
        exact ⟨induction.mpr (fun index included => member index (by omega)),
          member count (by omega)⟩

theorem prefixInter_antitone (sets : Nat → Set α) : AntitoneFamily (prefixInter sets) := by
  intro first second included value member
  apply (mem_prefixInter sets first value).mpr
  intro index before
  exact (mem_prefixInter sets second value).mp member index (by omega)

theorem iInter_prefixInter (sets : Nat → Set α) :
    iInter (prefixInter sets) = iInter sets := by
  apply ext
  intro value
  constructor
  · intro member index
    exact (mem_prefixInter sets (index + 1) value).mp (member (index + 1)) index (by omega)
  · intro member count
    exact (mem_prefixInter sets count value).mpr (fun index _ => member index)

end Set

end

end Problib.Measure
