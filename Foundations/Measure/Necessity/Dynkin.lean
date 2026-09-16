module

public import Foundations.Measure.Additive.Dirac
public import Foundations.Measure.Additive.Finite
public import Foundations.Measure.Dynkin.Uniqueness

set_option autoImplicit false

namespace Foundations.Measure.Necessity

open Foundations.Measure
open Foundations.Real

public section

def checkerboardFirst : Set (Bool × Bool) :=
  fun value => value.1 = true

def checkerboardSecond : Set (Bool × Bool) :=
  fun value => value.2 = true

def checkerboardCorner : Set (Bool × Bool) :=
  Set.inter checkerboardFirst checkerboardSecond

def checkerboardGenerators : Set (Set (Bool × Bool)) :=
  fun set => set = Set.univ ∨
    set = checkerboardFirst ∨ set = checkerboardSecond

theorem checkerboardGenerators_contains_univ :
    checkerboardGenerators Set.univ :=
  Or.inl rfl

theorem checkerboardGenerators_not_piSystem :
    ¬PiSystem checkerboardGenerators := by
  intro intersectionClosed
  have cornerGenerated := intersectionClosed
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  rcases cornerGenerated with cornerUniv | cornerFirst | cornerSecond
  · have cornerMember : checkerboardCorner (false, false) := by
      unfold checkerboardCorner
      rw [cornerUniv]
      exact True.intro
    exact Bool.noConfusion cornerMember.1
  · have cornerMember : checkerboardCorner (true, false) := by
      unfold checkerboardCorner
      rw [cornerFirst]
      exact rfl
    exact Bool.noConfusion cornerMember.2
  · have cornerMember : checkerboardCorner (false, true) := by
      unfold checkerboardCorner
      rw [cornerSecond]
      exact rfl
    exact Bool.noConfusion cornerMember.1

def checkerboardSpace : Space (Bool × Bool) :=
  Space.generated checkerboardGenerators

theorem checkerboardFirst_measurable :
    checkerboardSpace.Measurable checkerboardFirst :=
  Space.generated_contains (Or.inr (Or.inl rfl))

theorem checkerboardSecond_measurable :
    checkerboardSpace.Measurable checkerboardSecond :=
  Space.generated_contains (Or.inr (Or.inr rfl))

theorem checkerboardCorner_measurable :
    checkerboardSpace.Measurable checkerboardCorner :=
  checkerboardSpace.inter checkerboardFirst_measurable
    checkerboardSecond_measurable

noncomputable def checkerboardDiagonal : Measure checkerboardSpace :=
  Measure.add
    (Measure.dirac checkerboardSpace (false, false))
    (Measure.dirac checkerboardSpace (true, true))

noncomputable def checkerboardOffDiagonal : Measure checkerboardSpace :=
  Measure.add
    (Measure.dirac checkerboardSpace (false, true))
    (Measure.dirac checkerboardSpace (true, false))

theorem checkerboardDiagonal_finite :
    Measure.IsFinite checkerboardDiagonal := by
  apply Measure.IsFinite.add
  · constructor
    rw [Measure.dirac_apply_univ]
    exact True.intro
  · constructor
    rw [Measure.dirac_apply_univ]
    exact True.intro

theorem checkerboardOffDiagonal_finite :
    Measure.IsFinite checkerboardOffDiagonal := by
  apply Measure.IsFinite.add
  · constructor
    rw [Measure.dirac_apply_univ]
    exact True.intro
  · constructor
    rw [Measure.dirac_apply_univ]
    exact True.intro

theorem checkerboardMeasures_agree_on_generators
    (set : Set (Bool × Bool)) (generated : checkerboardGenerators set) :
    checkerboardDiagonal set = checkerboardOffDiagonal set := by
  rcases generated with univ | first | second
  · subst set
    unfold checkerboardDiagonal checkerboardOffDiagonal
    rw [Measure.add_apply_measurable _ _ checkerboardSpace.univ,
      Measure.add_apply_measurable _ _ checkerboardSpace.univ,
      Measure.dirac_apply_univ, Measure.dirac_apply_univ,
      Measure.dirac_apply_univ, Measure.dirac_apply_univ]
  · subst set
    unfold checkerboardDiagonal checkerboardOffDiagonal
    rw [Measure.add_apply_measurable _ _ checkerboardFirst_measurable,
      Measure.add_apply_measurable _ _ checkerboardFirst_measurable,
      Measure.dirac_apply _ _ checkerboardFirst_measurable,
      Measure.dirac_apply _ _ checkerboardFirst_measurable,
      Measure.dirac_apply _ _ checkerboardFirst_measurable,
      Measure.dirac_apply _ _ checkerboardFirst_measurable]
    simp [checkerboardFirst, ENNReal.zeroAdd]
  · subst set
    unfold checkerboardDiagonal checkerboardOffDiagonal
    rw [Measure.add_apply_measurable _ _ checkerboardSecond_measurable,
      Measure.add_apply_measurable _ _ checkerboardSecond_measurable,
      Measure.dirac_apply _ _ checkerboardSecond_measurable,
      Measure.dirac_apply _ _ checkerboardSecond_measurable,
      Measure.dirac_apply _ _ checkerboardSecond_measurable,
      Measure.dirac_apply _ _ checkerboardSecond_measurable]
    simp [checkerboardSecond, ENNReal.zeroAdd, ENNReal.addZero]

theorem checkerboardDiagonal_corner :
    checkerboardDiagonal checkerboardCorner = ENNReal.one := by
  unfold checkerboardDiagonal
  rw [Measure.add_apply_measurable _ _ checkerboardCorner_measurable,
    Measure.dirac_apply _ _ checkerboardCorner_measurable,
    Measure.dirac_apply _ _ checkerboardCorner_measurable]
  simp [checkerboardCorner, Set.inter, checkerboardFirst,
    checkerboardSecond,
    ENNReal.zeroAdd]

theorem checkerboardOffDiagonal_corner :
    checkerboardOffDiagonal checkerboardCorner = ENNReal.zero := by
  unfold checkerboardOffDiagonal
  rw [Measure.add_apply_measurable _ _ checkerboardCorner_measurable,
    Measure.dirac_apply _ _ checkerboardCorner_measurable,
    Measure.dirac_apply _ _ checkerboardCorner_measurable]
  simp [checkerboardCorner, Set.inter, checkerboardFirst,
    checkerboardSecond,
    ENNReal.addZero]

theorem checkerboardMeasures_ne :
    checkerboardDiagonal ≠ checkerboardOffDiagonal := by
  intro equal
  have cornerEqual := congrArg
    (fun measure : Measure checkerboardSpace =>
      measure checkerboardCorner) equal
  rw [checkerboardDiagonal_corner,
    checkerboardOffDiagonal_corner] at cornerEqual
  exact ENNReal.oneNeZero cornerEqual

theorem pi_system_is_necessary_for_finite_measure_uniqueness :
    checkerboardSpace = Space.generated checkerboardGenerators ∧
      checkerboardGenerators Set.univ ∧
      Measure.IsFinite checkerboardDiagonal ∧
      Measure.IsFinite checkerboardOffDiagonal ∧
      (∀ set, checkerboardGenerators set →
        checkerboardDiagonal set = checkerboardOffDiagonal set) ∧
      checkerboardDiagonal ≠ checkerboardOffDiagonal ∧
      ¬PiSystem checkerboardGenerators :=
  ⟨rfl, checkerboardGenerators_contains_univ,
    checkerboardDiagonal_finite, checkerboardOffDiagonal_finite,
    checkerboardMeasures_agree_on_generators, checkerboardMeasures_ne,
    checkerboardGenerators_not_piSystem⟩

end

end Foundations.Measure.Necessity
