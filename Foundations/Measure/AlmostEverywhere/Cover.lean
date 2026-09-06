module

public import Foundations.Measure.AlmostEverywhere.Transport

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u v

variable {alpha : Type u} {beta : Sort v}
  {space : Space alpha} {measure : Measure space}

/-- A set is null when its restrictions to a countable covering family of
regions are null. The covering regions need not be measurable. -/
public theorem NullSet.of_restrict_cover {regions : Nat → Set alpha}
    (cover : Set.iUnion regions = Set.univ) {set : Set alpha}
    (nullRestrictions : ∀ index, (measure.restrict (regions index)).NullSet set) :
    measure.NullSet set := by
  classical
  have envelopes := fun index =>
    (nullRestrictions index).exists_measurable_superset
  let supersets : Nat → Set alpha := fun index =>
    Classical.choose (envelopes index)
  have properties := fun index => Classical.choose_spec (envelopes index)
  have nullPieces : ∀ index,
      measure.NullSet (Set.inter (supersets index) (regions index)) := by
    intro index
    change measure (Set.inter (supersets index) (regions index)) = ENNReal.zero
    rw [← measure.restrict_apply (regions index) (properties index).1]
    exact (properties index).2.2
  apply (NullSet.iUnion nullPieces).mono
  intro value member
  have covered : Set.iUnion regions value := by
    rw [cover]
    exact True.intro
  rcases covered with ⟨index, regionMember⟩
  exact ⟨index, (properties index).2.1 member, regionMember⟩

/-- A set is null if and only if each restriction to a countable covering family
is null. The covering regions need not be measurable. -/
public theorem null_iff_forall_restrict {regions : Nat → Set alpha}
    (cover : Set.iUnion regions = Set.univ) {set : Set alpha} :
    measure.NullSet set ↔
      ∀ index, (measure.restrict (regions index)).NullSet set :=
  ⟨fun nullSet index => nullSet.restrict (regions index),
    NullSet.of_restrict_cover cover⟩

/-- A predicate holds almost everywhere when it holds almost everywhere on each
piece of a countable cover. The covering regions need not be measurable. -/
public theorem AE.of_restrict_cover {regions : Nat → Set alpha}
    (cover : Set.iUnion regions = Set.univ) {predicate : alpha → Prop}
    (holds : ∀ index, (measure.restrict (regions index)).AE predicate) :
    measure.AE predicate :=
  NullSet.of_restrict_cover cover holds

/-- A predicate holds almost everywhere if and only if it holds almost
everywhere on each piece of a countable cover. The covering regions need not be
measurable. -/
public theorem ae_iff_forall_restrict {regions : Nat → Set alpha}
    (cover : Set.iUnion regions = Set.univ) {predicate : alpha → Prop} :
    measure.AE predicate ↔
      ∀ index, (measure.restrict (regions index)).AE predicate :=
  null_iff_forall_restrict cover

/-- Two functions agree almost everywhere when they agree almost everywhere on
each piece of a countable cover. The covering regions need not be measurable. -/
public theorem AEEq.of_restrict_cover {regions : Nat → Set alpha}
    (cover : Set.iUnion regions = Set.univ) {left right : alpha → beta}
    (equal : ∀ index, (measure.restrict (regions index)).AEEq left right) :
    measure.AEEq left right :=
  AE.of_restrict_cover cover equal

end Foundations.Measure.Measure
