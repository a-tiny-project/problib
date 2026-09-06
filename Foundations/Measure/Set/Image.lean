module

public import Foundations.Measure.Set

set_option autoImplicit false

namespace Foundations.Measure.Set

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Forward image of a subset under a function. -/
@[expose] public def image (function : α → β) (region : Set α) : Set β :=
  fun output => ∃ input, region input ∧ function input = output

@[simp] public theorem image_empty (function : α → β) :
    image function Set.empty = Set.empty := by
  apply Set.ext
  intro output
  exact ⟨fun ⟨_, impossible, _⟩ => impossible, False.elim⟩

@[simp] public theorem image_univ (function : α → β) :
    image function Set.univ = Set.range function := by
  apply Set.ext
  intro output
  exact ⟨fun ⟨input, _, equal⟩ => ⟨input, equal⟩,
    fun ⟨input, equal⟩ => ⟨input, True.intro, equal⟩⟩

@[simp] public theorem image_id (region : Set α) :
    image (fun input => input) region = region := by
  apply Set.ext
  intro output
  exact ⟨fun ⟨input, member, equal⟩ => equal ▸ member,
    fun member => ⟨output, member, rfl⟩⟩

public theorem image_comp (before : α → β) (after : β → γ) (region : Set α) :
    image (fun input => after (before input)) region = image after (image before region) := by
  apply Set.ext
  intro output
  constructor
  · rintro ⟨input, member, equal⟩
    exact ⟨before input, ⟨input, member, rfl⟩, equal⟩
  · rintro ⟨middle, ⟨input, member, middleEqual⟩, equal⟩
    exact ⟨input, member, (congrArg after middleEqual).trans equal⟩

public theorem image_mono (function : α → β) {left right : Set α}
    (included : Set.Subset left right) : Set.Subset (image function left) (image function right) := by
  rintro output ⟨input, member, equal⟩
  exact ⟨input, included member, equal⟩

public theorem image_iUnion (function : α → β) (regions : Nat → Set α) :
    image function (Set.iUnion regions) = Set.iUnion (fun index => image function (regions index)) := by
  apply Set.ext
  intro output
  constructor
  · rintro ⟨input, ⟨index, member⟩, equal⟩
    exact ⟨index, input, member, equal⟩
  · rintro ⟨index, input, member, equal⟩
    exact ⟨input, ⟨index, member⟩, equal⟩

public theorem image_pairwise (function : α → β) (injective : Function.Injective function)
    (regions : Nat → Set α) (disjoint : Set.PairwiseDisjoint regions) :
    Set.PairwiseDisjoint (fun index => image function (regions index)) := by
  intro first second different output
  rintro ⟨left, leftMember, leftEqual⟩ ⟨right, rightMember, rightEqual⟩
  have same := injective (leftEqual.trans rightEqual.symm)
  subst right
  exact disjoint first second different leftMember rightMember

public theorem preimage_image (function : α → β) (injective : Function.Injective function)
    (region : Set α) : Set.preimage function (image function region) = region := by
  apply Set.ext
  intro input
  exact ⟨fun ⟨other, member, equal⟩ => injective equal ▸ member,
    fun member => ⟨input, member, rfl⟩⟩

public theorem image_preimage (function : α → β) (region : Set β) :
    image function (Set.preimage function region) = Set.inter region (Set.range function) := by
  apply Set.ext
  intro output
  constructor
  · rintro ⟨input, member, equal⟩
    exact ⟨equal ▸ member, input, equal⟩
  · rintro ⟨member, input, equal⟩
    exact ⟨input, (show region (function input) from equal.symm ▸ member), equal⟩

public theorem image_preimage_subset (function : α → β) (region : Set β) :
    Set.Subset (image function (Set.preimage function region)) region := by
  intro output member
  rw [image_preimage] at member
  exact member.1

public theorem image_inter_preimage (function : α → β) (source : Set α) (target : Set β) :
    image function (Set.inter source (Set.preimage function target)) =
      Set.inter (image function source) target := by
  apply Set.ext
  intro output
  constructor
  · rintro ⟨input, ⟨sourceMember, targetMember⟩, equal⟩
    exact ⟨⟨input, sourceMember, equal⟩, equal ▸ targetMember⟩
  · rintro ⟨⟨input, sourceMember, equal⟩, targetMember⟩
    exact ⟨input, ⟨sourceMember, (show target (function input) from equal.symm ▸ targetMember)⟩, equal⟩

@[simp] public theorem range_subtype (region : Set α) :
    Set.range (fun value : {input : α // region input} => value.val) = region := by
  apply Set.ext
  intro input
  exact ⟨fun ⟨value, equal⟩ => equal ▸ value.property,
    fun member => ⟨⟨input, member⟩, rfl⟩⟩

public theorem image_subtype_preimage (region target : Set α) :
    image (fun value : {input : α // region input} => value.val)
      (Set.preimage (fun value : {input : α // region input} => value.val) target) =
      Set.inter target region := by
  rw [image_preimage, range_subtype]

end Foundations.Measure.Set
