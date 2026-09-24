import Problib.Inference.Derivative.Source.Affine
import Problib.Inference.Derivative.Source.Reverse

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source.Affine.Reverse

open Problib.Linear.Rational
open Problib.Probability
open Normalization

/-- The affine example's symbolic interpreter retains the existing linear
residual syntax. The selected source term uses no sampling primitives. -/
def normalizer : Finite.Normalizer Unit 1 where
  pureOutcome := ()
  model := {
    normalReparameterized := fun mean _scale continuation => continuation mean
    normalReinforce := fun mean _scale continuation => continuation mean
  }

def symbolicEnvironment (point slope offset : Rat) :
    Target.Environment Rat (Finite.SymbolicTangent Unit 1) [Ty.scalar.derivative] :=
  .cons (slope * point + offset, .coordinate (fun _ => slope) 0 0) .nil

def tangentRelated (direction : Vector 1) :
    Structural.TangentRelation (Finite.SymbolicTangent Unit 1) Rat :=
  fun residual tangent => residual.apply () direction 0 = tangent

theorem reconstruction (point slope offset : Rat) :
    Finite.ReconstructionCertificate term normalizer (target point slope offset)
      (symbolicEnvironment point slope offset) tangentRelated := by
  constructor
  · intro direction
    change Matrix.apply (Matrix.zero 1 1) direction 0 = 0
    simp [Matrix.apply, Matrix.zero, finSum_zero]
  · intro direction
    refine .cons ⟨rfl, ?_⟩ .nil
    change FirstOrder.Linear.Program.apply (.coordinate (fun _ : Unit => slope) 0 0)
      () direction 0 = slope * direction 0
    simp [FirstOrder.Linear.Program.apply, FirstOrder.Linear.Program.denote,
      Matrix.apply, finSum_one_dimension]
  · intro direction
    exact .let_ _ _ (.pure _) (.pure _)
  · intro direction symbolicJet concreteJet related
    have tangent : symbolicJet.2.apply () direction = fun _ => concreteJet.2 := by
      apply Problib.Linear.Rational.Vector.ext
      intro row
      have rowEqual : row = 0 := Subsingleton.elim _ _
      subst row
      exact related.2
    change FinitePMF.dirac ((), (concreteJet.1, fun _ => concreteJet.2)) ≈ₚ
      FinitePMF.dirac ((), (symbolicJet.1, symbolicJet.2.apply () direction))
    rw [related.1, tangent]
    exact FinitePMF.Equivalent.refl _

/-- The actual ordered source term normalizes, unzips, and transposes to an
exact gradient for its affine parameter family. Every certificate is inhabited. -/
theorem gradient_expected (point slope offset : Rat) :
    let normal := Finite.Term.normalize term normalizer
      (symbolicEnvironment point slope offset)
    expectedVector
        (FirstOrder.Transpose.transform (FirstOrder.Unzip.transform normal)).law
        (fun sample =>
          (FirstOrder.Transpose.transform (FirstOrder.Unzip.transform normal)).residual.apply
            sample.2 scalarSeed) = gradient (jacobian slope) :=
  Source.Reverse.gradient_unbiased_finite term (source point slope offset)
    (target point slope offset) (jacobian slope) (Related point) (computationRelated point)
    (certificate point slope offset) normalizer (symbolicEnvironment point slope offset)
    tangentRelated (reconstruction point slope offset)

/-- The resulting finite reverse execution estimates the nonzero gradient two. -/
theorem nonzero_gradient :
    let normal := Finite.Term.normalize term normalizer (symbolicEnvironment 3 2 1)
    expectedVector
        (FirstOrder.Transpose.transform (FirstOrder.Unzip.transform normal)).law
        (fun sample =>
          (FirstOrder.Transpose.transform (FirstOrder.Unzip.transform normal)).residual.apply
            sample.2 scalarSeed) 0 = 2 := by
  simpa [gradient, scalarSeed, Matrix.transposeApply, Matrix.transpose, Matrix.apply,
    finSum_one_dimension, jacobian, Rat.mul_one] using congrFun (gradient_expected 3 2 1) 0

end Problib.Inference.Derivative.Source.Affine.Reverse
