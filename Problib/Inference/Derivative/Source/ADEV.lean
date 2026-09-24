import Problib.Inference.Derivative.Source.Certificate

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source

universe u v w

/-- Pointwise primal preservation for the typed first-order CPS ADEV transform.

It proves the complete pure, ordered-let, reparameterized-normal, and
REINFORCE fragment from exactly the corresponding composition and primitive
certificates. No probabilistic law is built into the syntax.
The family theorem in `Source.Family` carries differential and seed obligations. -/
theorem Term.adev_fundamental {Scalar Tangent : Type u}
    {Effect : Type u → Type v} {Estimate : Type w}
    (zero : Tangent) (sourceModel : Model Scalar Effect)
    (targetModel : Target.Model Scalar Tangent Estimate)
    (relation : ComputationRelation Scalar Tangent Effect Estimate)
    (certificate : Certificate sourceModel targetModel relation)
    {context : List Ty} {result : Ty} (term : Term Scalar context result) :
    ∀ {sourceEnvironment : Environment Scalar context}
      {targetEnvironment :
        Target.Environment Scalar Tangent (context.map Ty.derivative)},
      Environment.Related Scalar Tangent sourceEnvironment targetEnvironment →
      relation result
        (term.denote sourceModel sourceEnvironment)
        ((term.adev zero).denote targetModel targetEnvironment) := by
  induction term with
  | pure value =>
      intro sourceEnvironment targetEnvironment environmentsRelated
      exact certificate.composition.pure
        (value.adev_related zero environmentsRelated)
  | let_ first body firstInduction bodyInduction =>
      intro sourceEnvironment targetEnvironment environmentsRelated
      apply certificate.composition.bind (firstInduction environmentsRelated)
      intro source target valuesRelated
      exact bodyInduction (.cons valuesRelated environmentsRelated)
  | normalReparameterized mean scale =>
      intro sourceEnvironment targetEnvironment environmentsRelated
      exact certificate.reparameterizedNormal.sound
        (mean.adev_related zero environmentsRelated)
        (scale.adev_related zero environmentsRelated)
  | normalReinforce mean scale =>
      intro sourceEnvironment targetEnvironment environmentsRelated
      exact certificate.reinforceNormal.sound
        (mean.adev_related zero environmentsRelated)
        (scale.adev_related zero environmentsRelated)

end Problib.Inference.Derivative.Source
