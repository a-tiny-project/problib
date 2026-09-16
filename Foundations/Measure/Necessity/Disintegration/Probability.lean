module

public import Foundations.Measure.Necessity.Density
public import Foundations.Measure.Disintegration.Reconstruction
public import Foundations.Measure.Kernel.Product.Algebra

set_option autoImplicit false

namespace Foundations.Measure.Necessity.Disintegration.Probability

open Foundations.Measure
open Foundations.Real

open Foundations.Measure.Necessity

public section

/-- A constant kernel assigning mass two times the Dirac measure on Unit. -/
noncomputable def conditional : Kernel (Space.discrete Unit) (Space.discrete Unit) :=
  Kernel.const (Space.discrete Unit)
    (Measure.smul Density.two (Measure.dirac (Space.discrete Unit) ()))

/-- The constant mass-two Dirac kernel is finite. -/
theorem conditional_isFinite : Kernel.IsFinite conditional :=
  Kernel.IsFinite.const _ (Measure.IsFinite.smul Density.two (by trivial) (Measure.IsFinite.dirac _ ()))

/-- Evaluating the constant mass-two kernel on the whole space yields two. -/
theorem conditional_univ (input : Unit) : conditional input Set.univ = Density.two := by
  change Measure.smul Density.two (Measure.dirac (Space.discrete Unit) ()) Set.univ = _
  rw [Measure.smul_apply_measurable _ _ True.intro, Measure.dirac_apply_univ, ENNReal.mulOne]

/-- An s-finite joint measure formed from an infinite reference marginal and a constant mass-two conditional kernel. -/
noncomputable def joint : Measure (Space.product (Space.discrete Unit) (Space.discrete Unit)) :=
  Measure.reverseSemiproduct Density.reference conditional conditional_isFinite.toSFinite

/-- The joint measure formed from the infinite reference marginal and mass-two conditional kernel is s-finite. -/
noncomputable def joint_sFinite : Measure.SFinite joint :=
  (Density.reference_sFinite.semiproduct conditional_isFinite.toSFinite).map
    (fun value => (value.2, value.1)) (Space.swap_measurable _ _)

/-- The total mass of the joint measure is infinite. -/
theorem joint_univ : joint Set.univ = ENNReal.top := by
  rw [joint, Measure.reverseSemiproduct_apply _ _ _ (Space.product _ _).univ]
  have equal : (fun second => conditional second
      (Set.preimage (fun first => (first, second)) Set.univ)) =
      (fun _ : Unit => Density.two) := by
    funext input
    rw [Set.preimage_univ, conditional_univ]
  rw [equal, lintegral_const, Density.reference_univ,
    ENNReal.mulTopOfNeZero Density.two_ne_zero]

/-- The second marginal of the joint measure equals the infinite reference measure. -/
theorem marginal_eq : Measure.secondMarginal joint = Density.reference := by
  apply Measure.ext
  intro set _
  classical
  by_cases member : set ()
  · have equal : set = Set.univ := by
      apply Set.ext
      intro input
      cases input
      exact ⟨fun _ => True.intro, fun _ => member⟩
    rw [equal, Measure.secondMarginal_apply _ True.intro,
      Set.preimage_univ, joint_univ, Density.reference_univ]
  · have equal : set = Set.empty := by
      apply Set.ext
      intro input
      cases input
      exact ⟨fun present => member present, False.elim⟩
    rw [equal, (Measure.secondMarginal joint).empty_apply, Density.reference.empty_apply]

/-- An exact disintegration of the joint measure using the mass-two conditional kernel. -/
noncomputable def disintegration : Measure.Disintegration joint where
  conditional := conditional
  conditionalSFinite := conditional_isFinite.toSFinite
  reconstruction := by
    rw [Measure.Disintegrates, marginal_eq]
    rfl

/-- The mass-two conditional measure is not a probability measure. -/
theorem conditional_not_probability (input : Unit) : ¬Measure.IsProbability (conditional input) := by
  intro probability
  have mass := probability.univ_eq_one
  rw [conditional_univ] at mass
  exact Density.one_ne_two mass.symm

/-- The disintegration using the mass-two conditional kernel does not have probability fibers almost everywhere under its second marginal. -/
theorem not_probability_ae : ¬(Measure.secondMarginal joint).AE
    (fun input => Measure.IsProbability (disintegration.conditional input)) := by
  intro probability
  have failed : Set.complement
      (fun input => Measure.IsProbability (disintegration.conditional input)) = Set.univ := by
    apply Set.ext
    intro input
    exact ⟨fun _ => True.intro, fun _ => conditional_not_probability input⟩
  change Measure.secondMarginal joint (Set.complement
    (fun input => Measure.IsProbability (disintegration.conditional input))) = ENNReal.zero at probability
  rw [failed, marginal_eq, Density.reference_univ] at probability
  exact ENNReal.topNeFinite NNReal.zero probability

/-- The second marginal of the joint measure is not sigma-finite. -/
theorem marginal_not_sigmaFinite : ¬Nonempty (Measure.SigmaFinite (Measure.secondMarginal joint)) := by
  rw [marginal_eq]
  exact Density.reference_not_sigmaFinite

/-- There exists an s-finite joint measure with an exact disintegration whose fibers are not probability almost everywhere. -/
theorem sFinite_disintegration_not_probability_ae :
    ∃ measure : Measure (Space.product (Space.discrete Unit) (Space.discrete Unit)),
      Nonempty (Measure.SFinite measure) ∧
      ∃ selection : Measure.Disintegration measure,
        ¬(Measure.secondMarginal measure).AE (fun input => Measure.IsProbability (selection.conditional input)) :=
  ⟨joint, ⟨joint_sFinite⟩, disintegration, not_probability_ae⟩

end

end Foundations.Measure.Necessity.Disintegration.Probability
