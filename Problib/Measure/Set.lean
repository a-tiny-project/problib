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

@[ext] theorem ext {left right : Set α}
    (equal : ∀ value, left value ↔ right value) : left = right := by
  apply funext
  intro value
  exact propext (equal value)

@[simp] theorem mem_empty (value : α) : ¬value ∈ (empty : Set α) :=
  id

@[simp] theorem mem_univ (value : α) : value ∈ (univ : Set α) :=
  True.intro

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

theorem empty_subset (set : Set α) : Subset empty set :=
  fun {_} member => False.elim member

theorem subset_univ (set : Set α) : Subset set univ :=
  fun {_} _ => True.intro

theorem subset_union_left (left right : Set α) :
    Subset left (union left right) :=
  fun {_} member => Or.inl member

theorem subset_union_right (left right : Set α) :
    Subset right (union left right) :=
  fun {_} member => Or.inr member

theorem union_subset {left right target : Set α}
    (leftTarget : Subset left target) (rightTarget : Subset right target) :
    Subset (union left right) target := by
  intro value member
  cases member with
  | inl leftMember => exact leftTarget leftMember
  | inr rightMember => exact rightTarget rightMember

theorem inter_subset_left (left right : Set α) :
    Subset (inter left right) left :=
  fun {_} member => member.1

theorem inter_subset_right (left right : Set α) :
    Subset (inter left right) right :=
  fun {_} member => member.2

theorem subset_inter {source left right : Set α}
    (sourceLeft : Subset source left) (sourceRight : Subset source right) :
    Subset source (inter left right) :=
  fun {_} member => ⟨sourceLeft member, sourceRight member⟩

theorem difference_subset (left right : Set α) :
    Subset (difference left right) left :=
  inter_subset_left left (complement right)

theorem subset_iUnion (sets : Nat → Set α) (index : Nat) :
    Subset (sets index) (iUnion sets) :=
  fun {_} member => ⟨index, member⟩

theorem iUnion_subset {sets : Nat → Set α} {target : Set α}
    (each : ∀ index, Subset (sets index) target) :
    Subset (iUnion sets) target := by
  intro value member
  rcases member with ⟨index, indexMember⟩
  exact each index indexMember

theorem iInter_subset (sets : Nat → Set α) (index : Nat) :
    Subset (iInter sets) (sets index) :=
  fun {_} member => member index

theorem subset_iInter {source : Set α} {sets : Nat → Set α}
    (each : ∀ index, Subset source (sets index)) :
    Subset source (iInter sets) :=
  fun {_} member index => each index member

theorem disjoint_symm {left right : Set α} :
    Disjoint left right → Disjoint right left :=
  fun disjoint {_} rightMember leftMember => disjoint leftMember rightMember

theorem empty_disjoint (set : Set α) : Disjoint empty set :=
  fun {_} emptyMember _ => False.elim emptyMember

theorem disjoint_empty (set : Set α) : Disjoint set empty :=
  disjoint_symm (empty_disjoint set)

theorem disjoint_of_subset_left {left middle right : Set α}
    (leftMiddle : Subset left middle) (middleRight : Disjoint middle right) :
    Disjoint left right :=
  fun {_} leftMember rightMember => middleRight (leftMiddle leftMember) rightMember

theorem disjoint_of_subset_right {left middle right : Set α}
    (middleRight : Subset middle right) (leftRight : Disjoint left right) :
    Disjoint left middle :=
  fun {_} leftMember middleMember => leftRight leftMember (middleRight middleMember)

theorem disjoint_iUnion_left {sets : Nat → Set α} {target : Set α}
    (each : ∀ index, Disjoint (sets index) target) :
    Disjoint (iUnion sets) target := by
  intro value member targetMember
  rcases member with ⟨index, indexMember⟩
  exact each index indexMember targetMember

theorem disjoint_iUnion_right {source : Set α} {sets : Nat → Set α}
    (each : ∀ index, Disjoint source (sets index)) :
    Disjoint source (iUnion sets) :=
  disjoint_symm (disjoint_iUnion_left fun index => disjoint_symm (each index))

theorem pairwiseDisjoint_symm {sets : Nat → Set α}
    (pairwise : PairwiseDisjoint sets) {first second : Nat}
    (different : first ≠ second) : Disjoint (sets second) (sets first) :=
  disjoint_symm (pairwise first second different)

@[simp] theorem complement_empty : complement (empty : Set α) = univ := by
  apply ext
  intro value
  exact ⟨fun _ => True.intro, fun _ falseMember => falseMember⟩

@[simp] theorem complement_univ : complement (univ : Set α) = empty := by
  apply ext
  intro value
  exact ⟨fun notTrue => notTrue True.intro, fun falseMember => False.elim falseMember⟩

@[simp] theorem union_empty_left (set : Set α) : union empty set = set := by
  apply ext
  intro value
  exact ⟨fun member => member.elim False.elim id, Or.inr⟩

@[simp] theorem union_empty_right (set : Set α) : union set empty = set := by
  apply ext
  intro value
  exact ⟨fun member => member.elim id False.elim, Or.inl⟩

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

theorem union_assoc (first second third : Set α) :
    union (union first second) third = union first (union second third) := by
  apply ext
  intro value
  constructor
  · intro member
    cases member with
    | inl firstOrSecond =>
        exact firstOrSecond.elim Or.inl (fun secondMember => Or.inr (Or.inl secondMember))
    | inr thirdMember => exact Or.inr (Or.inr thirdMember)
  · intro member
    cases member with
    | inl firstMember => exact Or.inl (Or.inl firstMember)
    | inr secondOrThird =>
        exact secondOrThird.elim (fun secondMember => Or.inl (Or.inr secondMember)) Or.inr

theorem inter_assoc (first second third : Set α) :
    inter (inter first second) third = inter first (inter second third) := by
  apply ext
  intro value
  exact ⟨fun member => ⟨member.1.1, member.1.2, member.2⟩,
    fun member => ⟨⟨member.1, member.2.1⟩, member.2.2⟩⟩

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
