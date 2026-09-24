module

public import Problib.Measure.Additive.Core

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- A set is outer-null when its outer measure vanishes.
The definition requires no measurability, measure-completeness, or
finiteness hypotheses. -/
@[expose] public def NullSet (measure : Measure space) (set : Set alpha) : Prop :=
  measure set = ENNReal.zero

public theorem null_empty (measure : Measure space) :
    measure.NullSet Set.empty :=
  measure.empty_apply

public theorem NullSet.mono {measure : Measure space} {left right : Set alpha}
    (nullRight : measure.NullSet right) (included : Set.Subset left right) :
    measure.NullSet left := by
  apply ENNReal.eq_zero_of_le_zero
  exact nullRight ▸ measure.mono included

public theorem NullSet.union {measure : Measure space} {left right : Set alpha}
    (nullLeft : measure.NullSet left) (nullRight : measure.NullSet right) :
    measure.NullSet (Set.union left right) := by
  apply ENNReal.eq_zero_of_le_zero
  have bound := measure.union_le left right
  rw [nullLeft, nullRight, ENNReal.zero_add] at bound
  exact bound

public theorem NullSet.iUnion {measure : Measure space} {sets : Nat → Set alpha}
    (nullSets : ∀ index, measure.NullSet (sets index)) :
    measure.NullSet (Set.iUnion sets) := by
  apply ENNReal.eq_zero_of_le_zero
  have bound := measure.iUnion_le sets
  have totalZero : ENNReal.tsum (fun index => measure (sets index)) =
      ENNReal.zero := ENNReal.tsum_eq_zero_iff.mpr nullSets
  rw [totalZero] at bound
  exact bound

public theorem null_union_iff {measure : Measure space} {left right : Set alpha} :
    measure.NullSet (Set.union left right) ↔
      measure.NullSet left ∧ measure.NullSet right :=
  ⟨fun nullUnion =>
    ⟨nullUnion.mono (fun {_} member => Or.inl member),
      nullUnion.mono (fun {_} member => Or.inr member)⟩,
    fun both => both.1.union both.2⟩

public theorem null_iUnion_iff {measure : Measure space} {sets : Nat → Set alpha} :
    measure.NullSet (Set.iUnion sets) ↔
      ∀ index, measure.NullSet (sets index) :=
  ⟨fun nullUnion index =>
    nullUnion.mono (fun {_} member => ⟨index, member⟩),
    NullSet.iUnion⟩

/-- Two sets have identical measure when their symmetric differences are
outer-null. -/
public theorem measure_eq_of_null_difference {measure : Measure space}
    {left right : Set alpha}
    (leftNull : measure.NullSet (Set.difference left right))
    (rightNull : measure.NullSet (Set.difference right left)) :
    measure left = measure right := by
  classical
  have compare : ∀ {first second : Set alpha},
      measure.NullSet (Set.difference first second) →
      ENNReal.le (measure first) (measure second) := by
    intro first second nullDifference
    have included : Set.Subset first
        (Set.union second (Set.difference first second)) := by
      intro value member
      by_cases other : second value
      · exact Or.inl other
      · exact Or.inr ⟨member, other⟩
    have bound := ENNReal.le_trans (measure.mono included)
      (measure.union_le second (Set.difference first second))
    rw [nullDifference, ENNReal.add_zero] at bound
    exact bound
  exact ENNReal.le_antisymm (compare leftNull) (compare rightNull)

end Problib.Measure.Measure
