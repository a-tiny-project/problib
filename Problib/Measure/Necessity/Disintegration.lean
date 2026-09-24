module

public import Problib.Measure.Necessity.Disintegration.Probability
public import Problib.Measure.Necessity.Disintegration.Uniqueness
public import Problib.Measure.Additive.Counting
public import Problib.Measure.Disintegration.Reconstruction
public import Problib.Measure.StandardBorel
public import Problib.Measure.Integral.Lebesgue.Algebra
public import Problib.Measure.Kernel.Product.Uniqueness

set_option autoImplicit false

namespace Problib.Measure.Necessity.Disintegration

open Problib.Real

public section

universe u

/-- A kernel into an empty conditioned space cannot evaluate to a probability
measure on any fiber where an input point exists. -/
theorem empty_fiber_not_probability {beta : Type u}
    {parameter : Space beta} {emptySpace : Space Empty}
    (kernel : Kernel parameter emptySpace) (input : beta) :
    ¬Measure.IsProbability (kernel input) := by
  intro probability
  have wholeEmpty : (Set.univ : Set Empty) = Set.empty := by
    funext value
    cases value
  have normalized := probability.univ_eq_one
  rw [wholeEmpty, (kernel input).empty_apply] at normalized
  exact ENNReal.one_ne_zero normalized.symm

noncomputable def unitFinite :
    Measure.SigmaFinite (Measure.dirac (Space.discrete Unit) ()) :=
  Measure.SigmaFinite.ofFinite (Measure.IsFinite.dirac _ ())

noncomputable def joint :
    Measure (Space.product (Space.discrete Nat) (Space.discrete Unit)) :=
  Measure.prod Measure.counting (Measure.dirac (Space.discrete Unit) ())
    unitFinite.toSFinite

noncomputable def joint_sigmaFinite : Measure.SigmaFinite joint :=
  Measure.counting_sigmaFinite.prod unitFinite

def rectangle : Set (Nat × Unit) :=
  Set.product (fun value => value = 0) Set.univ

theorem rectangle_measurable :
    (Space.product (Space.discrete Nat) (Space.discrete Unit)).Measurable
      rectangle :=
  Space.product_set_measurable _ _ True.intro True.intro

theorem joint_rectangle : joint rectangle = ENNReal.one := by
  rw [joint, rectangle, Measure.prod_apply_product _ _ _
    True.intro True.intro, Measure.counting_singleton,
    Measure.dirac_apply_univ, ENNReal.mul_one]

theorem joint_univ : joint Set.univ = ENNReal.top := by
  have productUniv :
      (Set.univ : Set (Nat × Unit)) = Set.product Set.univ Set.univ := by
    apply Set.ext
    intro value
    exact ⟨fun _ => ⟨True.intro, True.intro⟩, fun _ => True.intro⟩
  rw [productUniv, joint, Measure.prod_apply_product _ _ _
    True.intro True.intro, Measure.counting_univ,
    Measure.dirac_apply_univ, ENNReal.mul_one]

theorem marginal_univ :
    Measure.secondMarginal joint Set.univ = ENNReal.top := by
  rw [Measure.secondMarginal_apply joint (Space.discrete Unit).univ,
    Set.preimage_univ, joint_univ]

theorem marginal_not_sigmaFinite :
    ¬Nonempty (Measure.SigmaFinite (Measure.secondMarginal joint)) := by
  rintro ⟨finite⟩
  have member : Set.iUnion finite.sets () := by
    rw [finite.cover]
    exact True.intro
  rcases member with ⟨index, included⟩
  have equal : finite.sets index = Set.univ := by
    apply Set.ext
    intro value
    cases value
    exact ⟨fun _ => True.intro, fun _ => included⟩
  have bound := finite.finite index
  rw [equal, marginal_univ] at bound
  exact bound

theorem reverse_rectangle
    (kernel : Kernel (Space.discrete Unit) (Space.discrete Nat))
    (kernelFinite : Kernel.IsSFinite kernel) :
    Measure.reverseSemiproduct (Measure.secondMarginal joint)
        kernel kernelFinite rectangle =
      ENNReal.mul (kernel () (fun value => value = 0)) ENNReal.top := by
  rw [Measure.reverseSemiproduct_apply _ _ _ rectangle_measurable]
  have constant :
      (fun second => kernel second
        (Set.preimage (fun first => (first, second)) rectangle)) =
      (fun _ : Unit => kernel () (fun value => value = 0)) := by
    funext second
    cases second
    apply congrArg (kernel ())
    apply Set.ext
    intro value
    exact ⟨fun member => member.1, fun member => ⟨member, True.intro⟩⟩
  rw [constant, lintegral_const, marginal_univ]

theorem joint_not_disintegrable :
    ¬Nonempty (Measure.Disintegration joint) := by
  rintro ⟨disintegration⟩
  have reconstruction := congrArg (fun measure : Measure
      (Space.product (Space.discrete Nat) (Space.discrete Unit)) =>
        measure rectangle) disintegration.reconstruction
  rw [reverse_rectangle, joint_rectangle] at reconstruction
  by_cases zero : disintegration.conditional ()
      (fun value => value = 0) = ENNReal.zero
  · rw [zero, ENNReal.zero_mul] at reconstruction
    exact ENNReal.one_ne_zero reconstruction.symm
  · rw [ENNReal.mul_top_of_ne_zero zero] at reconstruction
    exact ENNReal.top_ne_finite NNReal.one reconstruction

/-- Joint sigma-finiteness alone does not imply disintegration on standard
Borel spaces. -/
theorem sigmaFinite_joint_does_not_imply_disintegration :
    ¬(∀ {alpha beta : Type} {source : Space alpha} {target : Space beta}
      (measure : Measure (Space.product source target)),
      StandardBorel source → StandardBorel target →
      Measure.SigmaFinite measure → Nonempty (Measure.Disintegration measure)) := by
  intro select
  exact joint_not_disintegrable
    (select joint StandardBorel.natural StandardBorel.unit joint_sigmaFinite)


/-- Joint s-finiteness alone does not imply the existence of a disintegration. -/
public theorem s_finite_joint_does_not_imply_disintegration :
    ¬(∀ {alpha beta : Type} {source : Space alpha} {target : Space beta}
      (measure : Measure (Space.product source target)),
      StandardBorel source → Measure.SFinite measure → Nonempty (Measure.Disintegration measure)) := by
  intro select
  exact joint_not_disintegrable
    (select joint StandardBorel.natural joint_sigmaFinite.toSFinite)

end

end Problib.Measure.Necessity.Disintegration
