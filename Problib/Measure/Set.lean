module

namespace Problib.Measure

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

set_option autoImplicit false

public section

abbrev Set (α : Type u) := α → Prop

namespace Set

instance {α : Type u} : Membership α (Set α) where
  mem set value := set value

@[expose] def empty : Set α :=
  fun _ => False

@[expose] def univ : Set α :=
  fun _ => True

@[expose] def complement (set : Set α) : Set α :=
  fun value => ¬set value

@[expose] def union (left right : Set α) : Set α :=
  fun value => left value ∨ right value

@[expose] def inter (left right : Set α) : Set α :=
  fun value => left value ∧ right value

@[expose] def difference (left right : Set α) : Set α :=
  inter left (complement right)

@[expose] def iUnion (sets : Nat → Set α) : Set α :=
  fun value => ∃ index, sets index value

@[expose] def iInter (sets : Nat → Set α) : Set α :=
  fun value => ∀ index, sets index value

@[expose] def preimage (function : α → β) (set : Set β) : Set α :=
  fun value => set (function value)

@[expose] def product (left : Set α) (right : Set β) : Set (α × β) :=
  fun value => left value.1 ∧ right value.2

@[expose] def singleton (value : α) : Set α :=
  fun candidate => candidate = value

@[expose] def Subset (left right : Set α) : Prop :=
  ∀ ⦃value⦄, left value → right value

@[expose] def Nonempty (set : Set α) : Prop :=
  ∃ value, set value

@[expose] def Disjoint (left right : Set α) : Prop :=
  ∀ ⦃value⦄, left value → right value → False

@[expose] def PairwiseDisjoint (sets : Nat → Set α) : Prop :=
  ∀ first second, first ≠ second → Disjoint (sets first) (sets second)

@[expose] def MonotoneFamily (sets : Nat → Set α) : Prop :=
  ∀ ⦃first second⦄, first ≤ second → Subset (sets first) (sets second)

@[expose] def AntitoneFamily (sets : Nat → Set α) : Prop :=
  ∀ ⦃first second⦄, first ≤ second → Subset (sets second) (sets first)

@[expose] def range (function : α → β) : Set β :=
  fun value => ∃ input, function input = value

/-- The sequence `left, right, empty, empty, ...`, which presents a binary
union as a countable one. -/
@[expose] def pair (left right : Set α) : Nat → Set α
  | 0 => left
  | 1 => right
  | _ + 2 => empty

@[ext] theorem ext {left right : Set α}
    (equal : ∀ value, left value ↔ right value) : left = right := by
  apply funext
  intro value
  exact propext (equal value)

@[simp] theorem mem_empty (value : α) : ¬value ∈ (empty : Set α) :=
  id

@[simp] theorem mem_complement (set : Set α) (value : α) :
    value ∈ complement set ↔ ¬value ∈ set :=
  Iff.rfl

@[simp] theorem mem_union (left right : Set α) (value : α) :
    value ∈ union left right ↔ value ∈ left ∨ value ∈ right :=
  Iff.rfl

@[simp] theorem mem_inter (left right : Set α) (value : α) :
    value ∈ inter left right ↔ value ∈ left ∧ value ∈ right :=
  Iff.rfl

@[simp] theorem mem_iUnion (sets : Nat → Set α) (value : α) :
    value ∈ iUnion sets ↔ ∃ index, value ∈ sets index :=
  Iff.rfl

@[simp] theorem mem_iInter (sets : Nat → Set α) (value : α) :
    value ∈ iInter sets ↔ ∀ index, value ∈ sets index :=
  Iff.rfl

@[simp] theorem mem_preimage (function : α → β) (set : Set β) (value : α) :
    value ∈ preimage function set ↔ function value ∈ set :=
  Iff.rfl

@[simp] theorem mem_range (function : α → β) (value : β) :
    value ∈ range function ↔ ∃ input, function input = value :=
  Iff.rfl

theorem subset_refl (set : Set α) : Subset set set :=
  fun {_} member => member

theorem subset_trans {first second third : Set α}
    (firstSecond : Subset first second) (secondThird : Subset second third) :
    Subset first third :=
  fun {_} member => secondThird (firstSecond member)

theorem subset_antisymm {left right : Set α}
    (leftRight : Subset left right) (rightLeft : Subset right left) :
    left = right := by
  apply ext
  intro value
  exact ⟨fun member => leftRight member, fun member => rightLeft member⟩

theorem subset_univ (set : Set α) : Subset set univ :=
  fun {_} _ => True.intro

theorem inter_subset_left (left right : Set α) :
    Subset (inter left right) left :=
  fun {_} member => member.1

theorem inter_subset_right (left right : Set α) :
    Subset (inter left right) right :=
  fun {_} member => member.2

theorem difference_subset (left right : Set α) :
    Subset (difference left right) left :=
  inter_subset_left left (complement right)

theorem subset_iUnion (sets : Nat → Set α) (index : Nat) :
    Subset (sets index) (iUnion sets) :=
  fun {_} member => ⟨index, member⟩

theorem iInter_subset (sets : Nat → Set α) (index : Nat) :
    Subset (iInter sets) (sets index) :=
  fun {_} member => member index

theorem disjoint_symm {left right : Set α} :
    Disjoint left right → Disjoint right left :=
  fun disjoint {_} rightMember leftMember => disjoint leftMember rightMember

theorem empty_disjoint (set : Set α) : Disjoint empty set :=
  fun {_} emptyMember _ => False.elim emptyMember

theorem disjoint_empty (set : Set α) : Disjoint set empty :=
  disjoint_symm (empty_disjoint set)

theorem iUnion_pair (left right : Set α) :
    iUnion (pair left right) = union left right := by
  apply ext
  intro value
  constructor
  · rintro ⟨index, member⟩
    match index, member with
    | 0, member => exact Or.inl member
    | 1, member => exact Or.inr member
  · rintro (member | member)
    · exact ⟨0, member⟩
    · exact ⟨1, member⟩

theorem pairwiseDisjoint_pair {left right : Set α} (disjoint : Disjoint left right) :
    PairwiseDisjoint (pair left right) := by
  intro first second different value firstMember secondMember
  match first, second, firstMember, secondMember with
  | 0, 0, _, _ => exact different rfl
  | 1, 1, _, _ => exact different rfl
  | 0, 1, firstMember, secondMember => exact disjoint firstMember secondMember
  | 1, 0, firstMember, secondMember => exact disjoint secondMember firstMember

@[simp] theorem complement_empty : complement (empty : Set α) = univ := by
  apply ext
  intro value
  exact ⟨fun _ => True.intro, fun _ falseMember => falseMember⟩

@[simp] theorem complement_univ : complement (univ : Set α) = empty := by
  apply ext
  intro value
  exact ⟨fun notTrue => notTrue True.intro, fun falseMember => False.elim falseMember⟩

@[simp] theorem inter_empty_left (set : Set α) : inter empty set = empty := by
  apply ext
  intro value
  exact ⟨fun member => member.1, False.elim⟩

@[simp] theorem inter_empty_right (set : Set α) : inter set empty = empty := by
  apply ext
  intro value
  exact ⟨fun member => member.2, False.elim⟩

@[simp] theorem inter_univ_left (set : Set α) : inter univ set = set := by
  apply ext
  intro value
  exact ⟨fun member => member.2, fun member => ⟨True.intro, member⟩⟩

@[simp] theorem inter_univ_right (set : Set α) : inter set univ = set := by
  apply ext
  intro value
  exact ⟨fun member => member.1, fun member => ⟨member, True.intro⟩⟩

theorem union_comm (left right : Set α) : union left right = union right left := by
  apply ext
  intro value
  exact ⟨Or.symm, Or.symm⟩

theorem inter_comm (left right : Set α) : inter left right = inter right left := by
  apply ext
  intro value
  exact ⟨fun member => ⟨member.2, member.1⟩,
    fun member => ⟨member.2, member.1⟩⟩

theorem inter_iUnion (set : Set α) (sets : Nat → Set α) :
    inter set (iUnion sets) = iUnion (fun index => inter set (sets index)) := by
  apply ext
  intro value
  constructor
  · rintro ⟨setMember, index, indexMember⟩
    exact ⟨index, setMember, indexMember⟩
  · rintro ⟨index, setMember, indexMember⟩
    exact ⟨setMember, index, indexMember⟩

theorem iUnion_inter (sets : Nat → Set α) (set : Set α) :
    inter (iUnion sets) set = iUnion (fun index => inter (sets index) set) := by
  rw [inter_comm, inter_iUnion]
  apply congrArg iUnion
  apply funext
  intro index
  exact inter_comm set (sets index)

theorem inter_difference_disjoint (left right : Set α) :
    Disjoint (inter left right) (difference left right) :=
  fun {_} inside outside => outside.2 inside.2

theorem inter_union_difference (left right : Set α) :
    union (inter left right) (difference left right) = left := by
  classical
  apply ext
  intro value
  constructor
  · intro member
    exact member.elim (fun inside => inside.1) (fun outside => outside.1)
  · intro leftMember
    by_cases rightMember : right value
    · exact Or.inl ⟨leftMember, rightMember⟩
    · exact Or.inr ⟨leftMember, rightMember⟩

theorem union_difference_absorb (left right : Set α) :
    union left (difference right left) = union left right := by
  classical
  apply ext
  intro value
  constructor
  · intro member
    exact member.elim Or.inl (fun outside => Or.inr outside.1)
  · intro member
    cases member with
    | inl leftMember => exact Or.inl leftMember
    | inr rightMember =>
        by_cases leftMember : left value
        · exact Or.inl leftMember
        · exact Or.inr ⟨rightMember, leftMember⟩

@[simp] theorem preimage_empty (function : α → β) :
    preimage function empty = empty :=
  rfl

@[simp] theorem preimage_univ (function : α → β) :
    preimage function univ = univ :=
  rfl

@[simp] theorem preimage_complement (function : α → β) (set : Set β) :
    preimage function (complement set) = complement (preimage function set) :=
  rfl

@[simp] theorem preimage_union (function : α → β) (left right : Set β) :
    preimage function (union left right) =
      union (preimage function left) (preimage function right) :=
  rfl

@[simp] theorem preimage_inter (function : α → β) (left right : Set β) :
    preimage function (inter left right) =
      inter (preimage function left) (preimage function right) :=
  rfl

@[simp] theorem preimage_iUnion (function : α → β) (sets : Nat → Set β) :
    preimage function (iUnion sets) =
      iUnion (fun index => preimage function (sets index)) :=
  rfl

@[simp] theorem preimage_iInter (function : α → β) (sets : Nat → Set β) :
    preimage function (iInter sets) =
      iInter (fun index => preimage function (sets index)) :=
  rfl

@[simp] theorem preimage_identity (set : Set α) :
    preimage (fun value => value) set = set :=
  rfl

@[simp] theorem preimage_comp (after : β → γ) (before : α → β) (set : Set γ) :
    preimage (fun value => after (before value)) set =
      preimage before (preimage after set) :=
  rfl

theorem complement_complement (set : Set α) : complement (complement set) = set := by
  classical
  funext value
  exact propext (Classical.not_not)

theorem complement_union (left right : Set α) :
    complement (union left right) = inter (complement left) (complement right) := by
  apply ext
  intro value
  exact ⟨fun outside => ⟨fun member => outside (Or.inl member),
      fun member => outside (Or.inr member)⟩,
    fun outside member => member.elim outside.1 outside.2⟩

theorem complement_inter (left right : Set α) :
    complement (inter left right) = union (complement left) (complement right) := by
  classical
  apply ext
  intro value
  by_cases inLeft : left value <;> by_cases inRight : right value <;>
    simp [complement, inter, union, inLeft, inRight]

theorem complement_iUnion (sets : Nat → Set α) :
    complement (iUnion sets) = iInter (fun index => complement (sets index)) := by
  apply ext
  intro value
  exact ⟨fun outside index member => outside ⟨index, member⟩,
    fun outside ⟨index, member⟩ => outside index member⟩

theorem complement_difference (left right : Set α) :
    complement (difference left right) = union (complement left) right := by
  change complement (inter left (complement right)) = _
  rw [complement_inter, complement_complement]

theorem complement_iInter (sets : Nat → Set α) :
    complement (iInter sets) = iUnion (fun index => complement (sets index)) := by
  classical
  apply ext
  intro value
  constructor
  · intro notAll
    apply Classical.byContradiction
    intro missing
    apply notAll
    intro index
    apply Classical.byContradiction
    intro outside
    exact missing ⟨index, outside⟩
  · rintro ⟨index, outside⟩ member
    exact outside (member index)

end Set

end

end Problib.Measure
