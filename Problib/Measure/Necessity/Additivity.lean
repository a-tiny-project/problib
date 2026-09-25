module

public import Problib.Measure.Additive.Dirac
public import Problib.Measure.Additive.Finite

set_option autoImplicit false

namespace Problib.Measure.Necessity

open Problib.Measure
open Problib.Real

public section

def repeatedUniv : Nat → Set Unit
  | 0 => Set.univ
  | 1 => Set.univ
  | _ + 2 => Set.empty

theorem repeatedUniv_measurable (index : Nat) :
    (Space.discrete Unit).Measurable (repeatedUniv index) :=
  True.intro

theorem repeatedUniv_not_pairwiseDisjoint :
    ¬Set.PairwiseDisjoint repeatedUniv := by
  intro pairwise
  have zeroOne := pairwise 0 1 (by decide)
  exact zeroOne (value := ()) True.intro True.intro

theorem iUnion_repeatedUniv :
    Set.iUnion repeatedUniv = Set.univ := by
  apply Set.ext
  intro value
  constructor
  · intro _
    exact True.intro
  · intro _
    exact ⟨0, True.intro⟩

theorem repeatedUniv_breaks_countable_additivity
    (measure : Measure (Space.discrete Unit))
    (univMass : measure Set.univ = ENNReal.one) :
    measure (Set.iUnion repeatedUniv) ≠
      ENNReal.tsum (fun index => measure (repeatedUniv index)) := by
  intro additive
  rw [iUnion_repeatedUniv, univMass] at additive
  have lower := ENNReal.partialSum_le_tsum
    (fun index => measure (repeatedUniv index)) 2
  change ENNReal.le
    (ENNReal.add
      (ENNReal.add ENNReal.zero (measure (repeatedUniv 0)))
      (measure (repeatedUniv 1)))
    (ENNReal.tsum (fun index => measure (repeatedUniv index))) at lower
  rw [show repeatedUniv 0 = Set.univ from rfl,
    show repeatedUniv 1 = Set.univ from rfl, univMass,
    ENNReal.zero_add] at lower
  rw [← additive] at lower
  have oneFinite : ENNReal.Finite ENNReal.one := by
    exact True.intro
  exact (ENNReal.lt_add_of_finite_of_positive oneFinite ENNReal.one_positive).2
    lower

theorem disjointness_is_necessary_for_countable_additivity :
    ¬Set.PairwiseDisjoint repeatedUniv ∧
      (Measure.dirac (Space.discrete Unit) ())
          (Set.iUnion repeatedUniv) ≠
        ENNReal.tsum (fun index =>
          (Measure.dirac (Space.discrete Unit) ())
            (repeatedUniv index)) :=
  ⟨repeatedUniv_not_pairwiseDisjoint,
    repeatedUniv_breaks_countable_additivity
      (Measure.dirac (Space.discrete Unit) ())
      (Measure.dirac_apply_univ (Space.discrete Unit) ())⟩

def decreasingTail (index : Nat) : Set Nat :=
  fun value => index ≤ value

theorem decreasingTail_measurable (index : Nat) :
    (Space.discrete Nat).Measurable (decreasingTail index) :=
  True.intro

theorem decreasingTail_antitone :
    Set.AntitoneFamily decreasingTail := by
  intro first second firstSecond value secondMember
  exact Nat.le_trans firstSecond secondMember

theorem decreasingTail_nonempty (index : Nat) :
    Set.Nonempty (decreasingTail index) :=
  ⟨index, Nat.le_refl index⟩

theorem iInter_decreasingTail :
    Set.iInter decreasingTail = Set.empty := by
  apply Set.ext
  intro value
  constructor
  · intro member
    exact (Nat.not_succ_le_self value) (member (value + 1))
  · intro member
    exact False.elim member

noncomputable def topOnNonemptyValue (set : Set Nat) : ENNReal := by
  classical
  exact if Set.Nonempty set then ENNReal.top else ENNReal.zero

noncomputable def topOnNonemptyOuter : OuterMeasure Nat where
  measure := topOnNonemptyValue
  empty := by
    classical
    unfold topOnNonemptyValue
    rw [if_neg]
    rintro ⟨value, member⟩
    exact member
  mono := by
    intro left right included
    classical
    unfold topOnNonemptyValue
    by_cases leftNonempty : Set.Nonempty left
    · have rightNonempty : Set.Nonempty right := by
        rcases leftNonempty with ⟨value, member⟩
        exact ⟨value, included member⟩
      simp only [if_pos leftNonempty, if_pos rightNonempty]
      exact ENNReal.le_refl ENNReal.top
    · simp only [if_neg leftNonempty]
      exact ENNReal.zero_le _
  iUnion_le := by
    intro sets
    classical
    by_cases unionNonempty : Set.Nonempty (Set.iUnion sets)
    · rcases unionNonempty with ⟨value, index, member⟩
      have termIncluded := ENNReal.term_le_tsum
        (fun current => topOnNonemptyValue (sets current))
        index
      unfold topOnNonemptyValue at termIncluded
      rw [if_pos ⟨value, member⟩] at termIncluded
      unfold topOnNonemptyValue
      rw [if_pos ⟨value, index, member⟩]
      exact termIncluded
    · unfold topOnNonemptyValue
      rw [if_neg unionNonempty]
      exact ENNReal.zero_le _

theorem topOnNonemptyOuter_isCaratheodory (region : Set Nat) :
    topOnNonemptyOuter.IsCaratheodory region := by
  intro set
  change topOnNonemptyValue set =
    ENNReal.add (topOnNonemptyValue (Set.inter set region))
      (topOnNonemptyValue (Set.difference set region))
  classical
  unfold topOnNonemptyValue
  by_cases setNonempty : Set.Nonempty set
  · rcases setNonempty with ⟨value, setMember⟩
    by_cases regionMember : region value
    · have interNonempty : Set.Nonempty (Set.inter set region) :=
        ⟨value, setMember, regionMember⟩
      rw [if_pos ⟨value, setMember⟩, if_pos interNonempty,
        ENNReal.top_add]
    · have differenceNonempty :
          Set.Nonempty (Set.difference set region) :=
        ⟨value, setMember, regionMember⟩
      rw [if_pos ⟨value, setMember⟩, if_pos differenceNonempty,
        ENNReal.add_top]
  · have interEmpty : ¬Set.Nonempty (Set.inter set region) := by
      rintro ⟨value, setMember, _⟩
      exact setNonempty ⟨value, setMember⟩
    have differenceEmpty :
        ¬Set.Nonempty (Set.difference set region) := by
      rintro ⟨value, setMember, _⟩
      exact setNonempty ⟨value, setMember⟩
    rw [if_neg setNonempty, if_neg interEmpty, if_neg differenceEmpty,
      ENNReal.add_zero]

noncomputable def topOnNonemptyMeasure :
    Measure (Space.discrete Nat) :=
  OuterMeasure.toMeasure topOnNonemptyOuter
    (fun set _ => topOnNonemptyOuter_isCaratheodory set)

theorem topOnNonemptyMeasure_apply (set : Set Nat) :
    topOnNonemptyMeasure set = topOnNonemptyValue set :=
  OuterMeasure.toMeasure_apply topOnNonemptyOuter
    (fun candidate _ => topOnNonemptyOuter_isCaratheodory candidate)
    True.intro

theorem topOnNonemptyValue_of_nonempty {set : Set Nat}
    (nonempty : Set.Nonempty set) :
    topOnNonemptyValue set = ENNReal.top := by
  classical
  unfold topOnNonemptyValue
  rw [if_pos nonempty]

theorem topOnNonemptyValue_empty :
    topOnNonemptyValue Set.empty = ENNReal.zero := by
  classical
  unfold topOnNonemptyValue
  rw [if_neg]
  rintro ⟨value, member⟩
  exact member

theorem topOnNonemptyMeasure_decreasingTail (index : Nat) :
    topOnNonemptyMeasure (decreasingTail index) = ENNReal.top := by
  rw [topOnNonemptyMeasure_apply,
    topOnNonemptyValue_of_nonempty (decreasingTail_nonempty index)]

theorem topOnNonemptyMeasure_first_not_finite :
    ¬ENNReal.Finite (topOnNonemptyMeasure (decreasingTail 0)) := by
  rw [topOnNonemptyMeasure_decreasingTail]
  exact id

theorem topOnNonemptyMeasure_not_finite :
    ¬Measure.IsFinite topOnNonemptyMeasure := by
  intro finite
  have impossible := finite.univ_finite
  rw [topOnNonemptyMeasure_apply,
    topOnNonemptyValue_of_nonempty
      (set := Set.univ) ⟨0, True.intro⟩] at impossible
  exact impossible

theorem topOnNonemptyMeasure_breaks_continuity_from_above :
    topOnNonemptyMeasure (Set.iInter decreasingTail) ≠
      ENNReal.iInf
        (fun index => topOnNonemptyMeasure (decreasingTail index)) := by
  have valuesEqual :
      (fun index => topOnNonemptyMeasure (decreasingTail index)) =
        (fun _ => ENNReal.top) := by
    funext index
    exact topOnNonemptyMeasure_decreasingTail index
  rw [iInter_decreasingTail, topOnNonemptyMeasure_apply,
    topOnNonemptyValue_empty, valuesEqual, ENNReal.iInf_const]
  exact ENNReal.finite_ne_top NNReal.zero

theorem finiteness_is_necessary_for_continuity_from_above :
    (∀ index,
      (Space.discrete Nat).Measurable (decreasingTail index)) ∧
      Set.AntitoneFamily decreasingTail ∧
      ¬Measure.IsFinite topOnNonemptyMeasure ∧
      ¬ENNReal.Finite
        (topOnNonemptyMeasure (decreasingTail 0)) ∧
      topOnNonemptyMeasure (Set.iInter decreasingTail) ≠
        ENNReal.iInf
          (fun index => topOnNonemptyMeasure (decreasingTail index)) :=
  ⟨decreasingTail_measurable, decreasingTail_antitone,
    topOnNonemptyMeasure_not_finite,
    topOnNonemptyMeasure_first_not_finite,
    topOnNonemptyMeasure_breaks_continuity_from_above⟩

end

end Problib.Measure.Necessity
