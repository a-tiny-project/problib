module

public import Problib.Measure.Null

set_option autoImplicit false

namespace Problib.Measure.Measure

universe u v w

variable {alpha : Type u} {beta : Sort v} {gamma : Sort w}
  {space : Space alpha} {measure : Measure space}

/-- A predicate holds almost everywhere when its failure set is outer-null. -/
@[expose] public def AE (measure : Measure space) (predicate : alpha → Prop) : Prop :=
  measure.NullSet (Set.complement predicate)

public theorem ae_of_forall {predicate : alpha → Prop}
    (holds : ∀ value, predicate value) : measure.AE predicate := by
  apply measure.null_empty.mono
  intro value failure
  exact failure (holds value)

public theorem AE.mono {left right : alpha → Prop} (holds : measure.AE left)
    (implication : ∀ value, left value → right value) : measure.AE right :=
  NullSet.mono holds (fun {value} failure member =>
    failure (implication value member))

public theorem AE.and {left right : alpha → Prop}
    (leftHolds : measure.AE left) (rightHolds : measure.AE right) :
    measure.AE (fun value => left value ∧ right value) := by
  classical
  apply (NullSet.union leftHolds rightHolds).mono
  intro value failure
  by_cases leftMember : left value
  · exact Or.inr (fun rightMember => failure ⟨leftMember, rightMember⟩)
  · exact Or.inl leftMember

public theorem ae_and_iff {left right : alpha → Prop} :
    measure.AE (fun value => left value ∧ right value) ↔
      measure.AE left ∧ measure.AE right :=
  ⟨fun both => ⟨both.mono (fun _ member => member.1),
    both.mono (fun _ member => member.2)⟩,
    fun both => both.1.and both.2⟩

public theorem ae_all_iff {predicates : Nat → alpha → Prop} :
    measure.AE (fun value => ∀ index, predicates index value) ↔
      ∀ index, measure.AE (predicates index) := by
  classical
  constructor
  · intro holds index
    exact holds.mono (fun _ member => member index)
  · intro holds
    apply (NullSet.iUnion holds).mono
    intro value failure
    exact Classical.not_forall.mp failure

/-- Every almost-everywhere predicate admits a measurable null exception set
outside of which the predicate holds everywhere. -/
public theorem AE.exists_null_exception {predicate : alpha → Prop}
    (holds : measure.AE predicate) :
    ∃ exceptional : Set alpha, space.Measurable exceptional ∧
      measure.NullSet exceptional ∧
      ∀ value, ¬exceptional value → predicate value := by
  classical
  rcases NullSet.exists_measurable_superset holds with
    ⟨exceptional, measurable, included, nullSet⟩
  refine ⟨exceptional, measurable, nullSet, ?_⟩
  intro value outside
  apply Classical.byContradiction
  intro failure
  exact outside (included failure)

/-- Two functions are almost-everywhere equal when their disagreement set is
outer-null. -/
@[expose] public def AEEq (measure : Measure space)
    (left right : alpha → beta) : Prop :=
  measure.AE (fun value => left value = right value)

public theorem AEEq.refl (function : alpha → beta) :
    measure.AEEq function function :=
  ae_of_forall (fun _ => rfl)

public theorem AEEq.symm {left right : alpha → beta}
    (equal : measure.AEEq left right) : measure.AEEq right left :=
  AE.mono equal (fun _ equality => equality.symm)

public theorem AEEq.trans {left middle right : alpha → beta}
    (first : measure.AEEq left middle) (second : measure.AEEq middle right) :
    measure.AEEq left right :=
  (AE.and first second).mono (fun _ both => both.1.trans both.2)

public theorem AEEq.comp {left right : alpha → beta}
    (equal : measure.AEEq left right) (function : beta → gamma) :
    measure.AEEq (fun value => function (left value))
      (fun value => function (right value)) :=
  AE.mono equal (fun _ equality => congrArg function equality)

public theorem ae_congr {left right : alpha → Prop}
    (equal : measure.AEEq left right) : measure.AE left ↔ measure.AE right :=
  ⟨fun leftHolds => (AE.and equal leftHolds).mono
    (fun _ both => both.1 ▸ both.2),
    fun rightHolds => (AE.and equal.symm rightHolds).mono
      (fun _ both => both.1 ▸ both.2)⟩

end Problib.Measure.Measure
