module

public import Foundations.Measure.Set.Family

namespace Foundations.Measure

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

set_option autoImplicit false

public section

structure Space (α : Type u) where
  Measurable : Set α → Prop
  empty : Measurable Set.empty
  complement : ∀ {set}, Measurable set → Measurable (Set.complement set)
  iUnion : ∀ {sets : Nat → Set α}, (∀ index, Measurable (sets index)) →
    Measurable (Set.iUnion sets)

namespace Space

@[ext] theorem ext {left right : Space α}
    (measurable : ∀ set, left.Measurable set ↔ right.Measurable set) :
    left = right := by
  cases left with
  | mk leftMeasurable leftEmpty leftComplement leftUnion =>
      cases right with
      | mk rightMeasurable rightEmpty rightComplement rightUnion =>
          have equal : leftMeasurable = rightMeasurable := by
            apply funext
            intro set
            exact propext (measurable set)
          cases equal
          rfl

theorem univ (space : Space α) : space.Measurable Set.univ := by
  have result := space.complement space.empty
  have equal : Set.complement (Set.empty : Set α) = Set.univ := by
    apply Set.ext
    intro value
    constructor
    · intro notFalse
      exact True.intro
    · intro trueValue falseValue
      exact falseValue
  rw [← equal]
  exact result

theorem union (space : Space α) {left right : Set α}
    (leftMeasurable : space.Measurable left)
    (rightMeasurable : space.Measurable right) :
    space.Measurable (Set.union left right) := by
  let sets : Nat → Set α := fun index =>
    match index with
    | 0 => left
    | _ + 1 => right
  have allMeasurable : ∀ index, space.Measurable (sets index) := by
    intro index
    cases index with
    | zero => exact leftMeasurable
    | succ index => exact rightMeasurable
  have unionMeasurable := space.iUnion allMeasurable
  have equal : Set.iUnion sets = Set.union left right := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨index, member⟩
      cases index with
      | zero => exact Or.inl member
      | succ index => exact Or.inr member
    · intro member
      cases member with
      | inl leftMember => exact ⟨0, leftMember⟩
      | inr rightMember => exact ⟨1, rightMember⟩
  rw [← equal]
  exact unionMeasurable

theorem inter (space : Space α) {left right : Set α}
    (leftMeasurable : space.Measurable left)
    (rightMeasurable : space.Measurable right) :
    space.Measurable (Set.inter left right) := by
  classical
  have complementsMeasurable := space.union
    (space.complement leftMeasurable) (space.complement rightMeasurable)
  have result := space.complement complementsMeasurable
  have equal :
      Set.complement (Set.union (Set.complement left) (Set.complement right)) =
        Set.inter left right := by
    apply Set.ext
    intro value
    change (¬(¬left value ∨ ¬right value)) ↔ left value ∧ right value
    constructor
    · intro neitherMissing
      constructor
      · exact Classical.byContradiction fun leftMissing =>
          neitherMissing (Or.inl leftMissing)
      · exact Classical.byContradiction fun rightMissing =>
          neitherMissing (Or.inr rightMissing)
    · rintro ⟨leftMember, rightMember⟩ missing
      cases missing with
      | inl leftMissing => exact leftMissing leftMember
      | inr rightMissing => exact rightMissing rightMember
  rw [← equal]
  exact result

theorem difference (space : Space α) {left right : Set α}
    (leftMeasurable : space.Measurable left)
    (rightMeasurable : space.Measurable right) :
    space.Measurable (Set.difference left right) :=
  space.inter leftMeasurable (space.complement rightMeasurable)

theorem iInter (space : Space α) {sets : Nat → Set α}
    (setsMeasurable : ∀ index, space.Measurable (sets index)) :
    space.Measurable (Set.iInter sets) := by
  classical
  have unionMeasurable := space.iUnion fun index =>
    space.complement (setsMeasurable index)
  have result := space.complement unionMeasurable
  have equal :
      Set.complement (Set.iUnion fun index => Set.complement (sets index)) =
        Set.iInter sets := by
    apply Set.ext
    intro value
    change (¬∃ index, ¬sets index value) ↔ ∀ index, sets index value
    constructor
    · intro noMissing index
      exact Classical.byContradiction fun missing =>
        noMissing ⟨index, missing⟩
    · intro allPresent missing
      rcases missing with ⟨index, absent⟩
      exact absent (allPresent index)
  rw [← equal]
  exact result

theorem prefixUnion_measurable (space : Space α) {sets : Nat → Set α}
    (measurable : ∀ index, space.Measurable (sets index)) (bound : Nat) :
    space.Measurable (Set.prefixUnion sets bound) := by
  induction bound with
  | zero => exact space.empty
  | succ bound induction => exact space.union induction (measurable bound)

theorem disjointed_measurable (space : Space α) {sets : Nat → Set α}
    (measurable : ∀ index, space.Measurable (sets index)) (index : Nat) :
    space.Measurable (Set.disjointed sets index) :=
  space.difference (measurable index)
    (space.prefixUnion_measurable measurable index)

@[expose] def discrete (α : Type u) : Space α where
  Measurable := fun _ => True
  empty := True.intro
  complement := fun _ => True.intro
  iUnion := fun _ => True.intro

theorem discrete_measurable (set : Set α) :
    (discrete α).Measurable set :=
  True.intro

inductive Generated {α : Type u} (generators : Set (Set α)) : Set α → Prop where
  | basic {set} : generators set → Generated generators set
  | empty : Generated generators Set.empty
  | complement {set} : Generated generators set →
      Generated generators (Set.complement set)
  | iUnion {sets : Nat → Set α} : (∀ index, Generated generators (sets index)) →
      Generated generators (Set.iUnion sets)

@[expose] def generated (generators : Set (Set α)) : Space α where
  Measurable := Generated generators
  empty := Generated.empty
  complement := Generated.complement
  iUnion := Generated.iUnion

@[expose] def indiscrete (α : Type u) : Space α where
  Measurable := fun set => set = Set.empty ∨ set = Set.univ
  empty := Or.inl rfl
  complement := by
    intro set measurable
    cases measurable with
    | inl empty =>
        subst set
        apply Or.inr
        apply Set.ext
        intro value
        constructor
        · intro notFalse
          exact True.intro
        · intro trueValue falseValue
          exact falseValue
    | inr univ =>
        subst set
        apply Or.inl
        apply Set.ext
        intro value
        constructor
        · intro notTrue
          exact notTrue True.intro
        · intro falseValue
          exact False.elim falseValue
  iUnion := by
    intro sets measurable
    classical
    by_cases containsUniv : ∃ index, sets index = Set.univ
    · apply Or.inr
      apply Set.ext
      intro value
      constructor
      · intro member
        exact True.intro
      · intro trueValue
        rcases containsUniv with ⟨index, equal⟩
        exact ⟨index, equal ▸ True.intro⟩
    · apply Or.inl
      apply Set.ext
      intro value
      constructor
      · rintro ⟨index, member⟩
        cases measurable index with
        | inl empty =>
            rw [empty] at member
            exact member
        | inr univ =>
            exact False.elim (containsUniv ⟨index, univ⟩)
      · intro falseValue
        exact False.elim falseValue

@[simp] theorem indiscrete_measurable_iff (set : Set α) :
    (indiscrete α).Measurable set ↔ set = Set.empty ∨ set = Set.univ :=
  Iff.rfl

theorem generated_contains {generators : Set (Set α)} {set : Set α}
    (member : generators set) : (generated generators).Measurable set :=
  Generated.basic member

theorem generated_minimal {generators : Set (Set α)} (target : Space α)
    (contains : ∀ {set}, generators set → target.Measurable set) :
    ∀ {set}, (generated generators).Measurable set → target.Measurable set := by
  intro set measurable
  induction measurable with
  | basic member => exact contains member
  | empty => exact target.empty
  | complement _ induction => exact target.complement induction
  | iUnion _ induction => exact target.iUnion induction

end Space

@[expose] def MeasurableMap (source : Space α) (target : Space β)
    (function : α → β) : Prop :=
  ∀ {set}, target.Measurable set →
    source.Measurable (Set.preimage function set)

namespace MeasurableMap

theorem identity (space : Space α) :
    MeasurableMap space space (fun value => value) := by
  intro set measurable
  exact measurable

theorem comp {first : Space α} {second : Space β} {third : Space γ}
    {after : β → γ} {before : α → β}
    (afterMeasurable : MeasurableMap second third after)
    (beforeMeasurable : MeasurableMap first second before) :
    MeasurableMap first third (fun value => after (before value)) := by
  intro set measurable
  exact beforeMeasurable (afterMeasurable measurable)

theorem intoGenerated {source : Space α} {generators : Set (Set β)}
    {function : α → β}
    (generatorsMeasurable : ∀ {set}, generators set →
      source.Measurable (Set.preimage function set)) :
    MeasurableMap source (Space.generated generators) function := by
  intro set measurable
  induction measurable with
  | basic member => exact generatorsMeasurable member
  | empty => exact source.empty
  | complement _ induction => exact source.complement induction
  | iUnion _ induction => exact source.iUnion induction

theorem toDiscrete (source : Space α) (function : α → β)
    (allPreimages : ∀ set, source.Measurable (Set.preimage function set)) :
    MeasurableMap source (Space.discrete β) function := by
  intro set _
  exact allPreimages set

theorem fromDiscrete (target : Space β) (function : α → β) :
    MeasurableMap (Space.discrete α) target function := by
  intro set _
  exact True.intro

/-- Constant map between arbitrary measurable spaces. The preimage of any set is
either `Set.univ` or `Set.empty`, both of which are measurable in any space. -/
theorem constant (source : Space α) (target : Space β) (value : β) :
    MeasurableMap source target (fun _ => value) := by
  intro set _
  classical
  by_cases member : set value
  · have equal : Set.preimage (fun _ : α => value) set = Set.univ := by
      apply Set.ext
      intro input
      exact ⟨fun _ => True.intro, fun _ => member⟩
    rw [equal]
    exact source.univ
  · have equal : Set.preimage (fun _ : α => value) set = Set.empty := by
      apply Set.ext
      intro input
      exact ⟨fun present => False.elim (member present), False.elim⟩
    rw [equal]
    exact source.empty

/-- Countable piecewise combination of measurable maps along a measurable
partition into `Nat`. Preimages decompose into a countable union of measurable
intersections. -/
theorem countablePiecewise {source : Space α} {target : Space β}
    {partition : α → Nat} {branches : Nat → α → β}
    (partitionMeasurable : ∀ index,
      source.Measurable (fun value => partition value = index))
    (branchesMeasurable : ∀ index,
      MeasurableMap source target (branches index)) :
    MeasurableMap source target (fun value => branches (partition value) value) := by
  intro set setMeasurable
  have unionMeasurable : source.Measurable
      (Set.iUnion fun index => Set.inter
        (fun value => partition value = index)
        (Set.preimage (branches index) set)) :=
    source.iUnion fun index => source.inter
      (partitionMeasurable index) (branchesMeasurable index setMeasurable)
  have equal : Set.preimage (fun value => branches (partition value) value) set =
      Set.iUnion fun index => Set.inter (fun value => partition value = index)
        (Set.preimage (branches index) set) := by
    apply Set.ext
    intro value
    constructor
    · intro member
      exact ⟨partition value, rfl, member⟩
    · rintro ⟨index, indexEqual, member⟩
      change set (branches index value) at member
      change set (branches (partition value) value)
      rw [indexEqual]
      exact member
  rw [equal]
  exact unionMeasurable

end MeasurableMap

namespace Space

@[expose] def comap (function : α → β) (target : Space β) : Space α :=
  generated fun sourceSet =>
    ∃ targetSet, target.Measurable targetSet ∧
      sourceSet = Set.preimage function targetSet

theorem comap_map (function : α → β) (target : Space β) :
    MeasurableMap (comap function target) target function := by
  intro set measurable
  exact Generated.basic ⟨set, measurable, rfl⟩

theorem comap_minimal {function : α → β} {source : Space α} {target : Space β}
    (functionMeasurable : MeasurableMap source target function) :
    ∀ {set}, (comap function target).Measurable set → source.Measurable set := by
  apply generated_minimal source
  rintro set ⟨targetSet, targetMeasurable, rfl⟩
  exact functionMeasurable targetMeasurable

/-- Characterize measurable sets in the pullback space as exact preimages of
target measurable sets. -/
theorem comap_measurable_iff (function : α → β) (target : Space β) (region : Set α) :
    (comap function target).Measurable region ↔
      ∃ targetRegion, target.Measurable targetRegion ∧ region = Set.preimage function targetRegion := by
  classical
  let inverseImages : Space α := {
    Measurable := fun set => ∃ targetSet, target.Measurable targetSet ∧
      set = Set.preimage function targetSet
    empty := ⟨Set.empty, target.empty, rfl⟩
    complement := by
      rintro set ⟨targetSet, measurable, rfl⟩
      exact ⟨Set.complement targetSet, target.complement measurable, rfl⟩
    iUnion := by
      intro sets measurable
      let targets := fun index => Classical.choose (measurable index)
      have targetsMeasurable : ∀ index, target.Measurable (targets index) :=
        fun index => (Classical.choose_spec (measurable index)).1
      refine ⟨Set.iUnion targets, target.iUnion targetsMeasurable, ?_⟩
      rw [Set.preimage_iUnion]
      apply congrArg Set.iUnion
      funext index
      exact (Classical.choose_spec (measurable index)).2
  }
  constructor
  · exact generated_minimal inverseImages (fun included => included)
  · rintro ⟨targetRegion, measurable, rfl⟩
    exact comap_map function target measurable

end Space

end

end Foundations.Measure
