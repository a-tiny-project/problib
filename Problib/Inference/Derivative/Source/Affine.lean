import Problib.Inference.Derivative.Source.Lowering

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source.Affine

open Problib.Linear.Rational
open Problib.Probability

/-- Exact rational affine variation along the selected direction.
This relation asserts an identity for every displacement, not a limit theorem. -/
def Related (point : Rat) (direction : Vector 1)
    (family : Rat → Rat) (jet : Target.Jet Rat Rat) : Prop :=
  ∀ displacement : Rat,
    family (point + displacement * direction 0) = jet.1 + displacement * jet.2

theorem related_unique (point : Rat) (direction : Vector 1)
    (family : Rat → Rat) (left right : Target.Jet Rat Rat)
    (leftRelated : Related point direction family left)
    (rightRelated : Related point direction family right) : left = right := by
  have primal : left.1 = right.1 := by
    simpa [Rat.zero_mul, Rat.add_zero] using (leftRelated 0).symm.trans (rightRelated 0)
  have tangent : left.2 = right.2 := by
    have sum := (leftRelated 1).symm.trans (rightRelated 1)
    simp only [Rat.one_mul, primal] at sum
    exact Rat.add_left_cancel right.1 sum
  exact Prod.ext primal tangent

theorem constant_related (point : Rat) (direction : Vector 1) (value : Rat) :
    Related point direction (fun _ => value) (value, 0) := by
  intro displacement
  simp [Rat.mul_zero, Rat.add_zero]

/-- A constant family cannot acquire an unrelated nonzero tangent. -/
theorem constant_rejects_nonzero_tangent (point : Rat) (direction : Vector 1) :
    ¬ Related point direction (fun _ => 0) (0, 1) := by
  intro related
  have impossible := related 1
  have zeroOne : (0 : Rat) = 1 := by
    simpa only [Prod.fst, Prod.snd, Rat.zero_add, Rat.one_mul] using impossible
  exact (by decide : (0 : Rat) ≠ 1) zeroOne

theorem affine_related (point slope offset : Rat) (direction : Vector 1) :
    Related point direction (fun parameter => slope * parameter + offset)
      (slope * point + offset, slope * direction 0) := by
  intro displacement
  change slope * (point + displacement * direction 0) + offset =
    slope * point + offset + displacement * (slope * direction 0)
  rw [Rat.mul_add, ← Rat.mul_assoc slope displacement (direction 0),
    Rat.mul_comm slope displacement, Rat.mul_assoc displacement slope (direction 0)]
  rw [Rat.add_assoc, Rat.add_comm (displacement * (slope * direction 0)) offset,
    ← Rat.add_assoc]

/-- The example uses the deterministic identity effect. Its unused primitive
handlers project the mean. They do not model Gaussian sampling or REINFORCE. -/
def sourceModel : Model Rat (fun Value => Value) where
  pure value := value
  bind value next := next value
  normalReparameterized mean _scale := mean
  normalReinforce mean _scale := mean

abbrev Estimate := FinitePMF (Unit × (Rat × Vector 1))

def targetModel : Target.Model Rat Rat Estimate where
  normalReparameterized mean _scale continuation := continuation mean
  normalReinforce mean _scale continuation := continuation mean

/-- A deterministic family and its exact CPS return of one related jet. -/
def computationRelated (point : Rat) (direction : Vector 1) :
    Family.ComputationRelation Rat Rat Rat (fun Value => Value) Estimate :=
  fun result source target => ∃ jet,
    Family.ValueRelated (Related point direction) result source jet ∧
      target = fun continuation => continuation jet

theorem familyCertificate (point : Rat) (direction : Vector 1) :
    Family.Certificate 0 sourceModel targetModel
      (Related point direction) (computationRelated point direction) := by
  constructor
  · exact constant_related point direction
  · intro result source target related
    exact ⟨target, related, rfl⟩
  · intro bound result sourceFirst targetFirst sourceBody targetBody firstRelated bodyRelated
    rcases firstRelated with ⟨firstJet, firstRelated, firstEqual⟩
    rcases bodyRelated sourceFirst firstJet firstRelated with ⟨resultJet, resultRelated, bodyEqual⟩
    refine ⟨resultJet, resultRelated, ?_⟩
    funext continuation
    rw [firstEqual]
    exact congrFun bodyEqual continuation
  · intro sourceMean sourceScale targetMean targetScale meanRelated _scaleRelated
    exact ⟨targetMean, meanRelated, rfl⟩
  · intro sourceMean sourceScale targetMean targetScale meanRelated _scaleRelated
    exact ⟨targetMean, meanRelated, rfl⟩

/-- An actual ordered source program returns its bound scalar variable. -/
def term : Term Rat [.scalar] .scalar :=
  .let_ (.pure (.var .head)) (.pure (.var .head))

/-- The input variable denotes the affine parameter family. Source syntax and
its ADEV transform remain unchanged. -/
def source (point slope offset : Rat) : SourceMeaning (fun Value => Value) [.scalar] where
  Parameter := Rat
  point := point
  model := sourceModel
  environment parameter := .cons (slope * parameter + offset) .nil
  primal value := value

def target (point slope offset : Rat) : DirectionalTarget Unit 1 [.scalar] where
  pureOutcome := ()
  model _direction := targetModel
  environment direction := .cons (slope * point + offset, slope * direction 0) .nil

def jacobian (slope : Rat) : Matrix 1 1 :=
  fun _ _ => slope

theorem certificate (point slope offset : Rat) :
    ExpectedCertificate term (source point slope offset) (target point slope offset)
      (jacobian slope) (Related point) (computationRelated point) := by
  constructor
  · exact related_unique point
  · intro direction
    exact .cons (affine_related point slope offset direction) .nil
  · exact familyCertificate point
  · intro direction
    change Related point direction (fun parameter => slope * parameter + offset)
      (slope * point + offset, Matrix.apply (jacobian slope) direction 0)
    simpa [Matrix.apply, jacobian, finSum_one_dimension] using
      affine_related point slope offset direction
  · intro direction sourceComputation targetComputation related
    rcases related with ⟨jet, jetRelated, targetEqual⟩
    simpa [targetEqual, target, source, scalarContinuation, expectedVector,
      Family.ValueRelated, Related] using jetRelated

/-- The source transform has the affine family's exact expected directional
derivative. The proof consumes an inhabited compositional certificate. -/
theorem expected (point slope offset : Rat) :
    ExpectedCorrectness (term.directionalExecution (target point slope offset))
      (slope * point + offset) (jacobian slope) :=
  term.directionalExecution_expected (source point slope offset) (target point slope offset)
    (jacobian slope) (Related point) (computationRelated point) (certificate point slope offset)

/-- The aligned seed for slope two cannot be replaced by a zero tangent. -/
theorem mismatched_seed_rejected :
    ¬ Related 3 (fun _ => 1) (fun parameter => 2 * parameter + 1) (7, 0) := by
  intro related
  have jets := related_unique 3 (fun _ => 1) _ _ _ related
    (affine_related 3 2 1 (fun _ => 1))
  have impossible : (0 : Rat) = 2 := by
    simpa [Rat.mul_one] using congrArg Prod.snd jets
  exact (by decide : (0 : Rat) ≠ 2) impossible

/-- The actual source ADEV execution observes primal seven and tangent ten. -/
theorem nonzero_execution :
    (term.directionalExecution (target 3 2 1) (fun _ => 5)).expectation
        (fun sample => sample.2.1) = 7 ∧
      (term.directionalExecution (target 3 2 1) (fun _ => 5)).expectation
        (fun sample => sample.2.2 0) = 10 := by
  constructor
  · apply ((expected 3 2 1).primal (fun _ => 5)).trans
    have product : (2 : Rat) * 3 = 6 := (Rat.natCast_mul 2 3).symm
    exact (congrArg (fun value : Rat => value + 1) product).trans
      (Rat.natCast_add 6 1).symm
  · have tangent := congrFun ((expected 3 2 1).jvp (fun _ => 5)) 0
    have exactTangent :
        (term.directionalExecution (target 3 2 1) (fun _ => 5)).expectation
          (fun sample => sample.2.2 0) = 2 * 5 := by
      simpa [expectedVector, Matrix.apply, jacobian, finSum_one_dimension] using tangent
    exact exactTangent.trans (Rat.natCast_mul 2 5).symm

end Problib.Inference.Derivative.Source.Affine
