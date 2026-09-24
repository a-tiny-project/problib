import Problib.Inference.Derivative.Source.Semantics

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source

universe u v w

/-- A pointwise relation between a source effect and an ADEV continuation
transformer. The pure rule leaves tangents unconstrained. Derivative correctness
requires the parameterized relations in `Source.Family` instead. -/
abbrev ComputationRelation (Scalar Tangent : Type u)
    (Effect : Type u → Type v) (Estimate : Type w) :=
  (result : Ty) → Effect (result.denote Scalar) →
    ((result.derivative.denote Scalar Tangent → Estimate) → Estimate) → Prop

/-- Certificates for ordered return and bind. No exchange law is present. -/
structure CompositionCertificate {Scalar Tangent : Type u}
    {Effect : Type u → Type v} {Estimate : Type w}
    (sourceModel : Model Scalar Effect)
    (relation : ComputationRelation Scalar Tangent Effect Estimate) : Prop where
  pure : {result : Ty} → {source : result.denote Scalar} →
    {target : result.derivative.denote Scalar Tangent} →
    result.Related Scalar Tangent source target →
      relation result (sourceModel.pure source) (fun continuation => continuation target)
  bind : {bound result : Ty} →
    {sourceFirst : Effect (bound.denote Scalar)} →
    {targetFirst :
      (bound.derivative.denote Scalar Tangent → Estimate) → Estimate} →
    {sourceBody : bound.denote Scalar → Effect (result.denote Scalar)} →
    {targetBody : bound.derivative.denote Scalar Tangent →
      (result.derivative.denote Scalar Tangent → Estimate) → Estimate} →
    relation bound sourceFirst targetFirst →
    (∀ source target, bound.Related Scalar Tangent source target →
      relation result (sourceBody source) (targetBody target)) →
    relation result
      (sourceModel.bind sourceFirst sourceBody)
      (fun continuation =>
        targetFirst fun target => targetBody target continuation)

/-- A pointwise semantic obligation for the reparameterized-normal CPS rule. -/
structure ReparameterizedNormalCertificate {Scalar Tangent : Type u}
    {Effect : Type u → Type v} {Estimate : Type w}
    (sourceModel : Model Scalar Effect)
    (targetModel : Target.Model Scalar Tangent Estimate)
    (relation : ComputationRelation Scalar Tangent Effect Estimate) : Prop where
  sound : {sourceMean sourceScale : Scalar} →
    {targetMean targetScale : Target.Jet Scalar Tangent} →
    Ty.Related Scalar Tangent .scalar sourceMean targetMean →
    Ty.Related Scalar Tangent .scalar sourceScale targetScale →
    relation .scalar
      (sourceModel.normalReparameterized sourceMean sourceScale)
      (targetModel.normalReparameterized targetMean targetScale)

/-- A pointwise semantic obligation for the score-function normal CPS rule. -/
structure ReinforceNormalCertificate {Scalar Tangent : Type u}
    {Effect : Type u → Type v} {Estimate : Type w}
    (sourceModel : Model Scalar Effect)
    (targetModel : Target.Model Scalar Tangent Estimate)
    (relation : ComputationRelation Scalar Tangent Effect Estimate) : Prop where
  sound : {sourceMean sourceScale : Scalar} →
    {targetMean targetScale : Target.Jet Scalar Tangent} →
    Ty.Related Scalar Tangent .scalar sourceMean targetMean →
    Ty.Related Scalar Tangent .scalar sourceScale targetScale →
    relation .scalar
      (sourceModel.normalReinforce sourceMean sourceScale)
      (targetModel.normalReinforce targetMean targetScale)

/-- Assumptions of the pointwise source ADEV fundamental theorem.
The relation preserves primal meaning without establishing a derivative. -/
structure Certificate {Scalar Tangent : Type u}
    {Effect : Type u → Type v} {Estimate : Type w}
    (sourceModel : Model Scalar Effect)
    (targetModel : Target.Model Scalar Tangent Estimate)
    (relation : ComputationRelation Scalar Tangent Effect Estimate) : Prop where
  composition : CompositionCertificate sourceModel relation
  reparameterizedNormal :
    ReparameterizedNormalCertificate sourceModel targetModel relation
  reinforceNormal : ReinforceNormalCertificate sourceModel targetModel relation

end Problib.Inference.Derivative.Source
