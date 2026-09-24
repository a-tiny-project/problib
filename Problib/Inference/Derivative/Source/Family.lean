import Problib.Inference.Derivative.Source.Semantics

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source.Family

universe u v w

/-- A scalar family is related to its primal and tangent at a selected seed.
The relation owns differentiability and seed alignment, not merely primal equality. -/
abbrev ScalarRelation (Parameter Scalar Tangent : Type u) :=
  (Parameter → Scalar) → Target.Jet Scalar Tangent → Prop

/-- Lift the scalar family relation through the existing first-order source types. -/
def ValueRelated {Parameter Scalar Tangent : Type u}
    (scalar : ScalarRelation Parameter Scalar Tangent) :
    (ty : Ty) → (Parameter → ty.denote Scalar) →
      ty.derivative.denote Scalar Tangent → Prop
  | .unit, _, _ => True
  | .scalar, source, target => scalar source target
  | .product left right, source, target =>
      ValueRelated scalar left (fun parameter => (source parameter).1) target.1 ∧
        ValueRelated scalar right (fun parameter => (source parameter).2) target.2

/-- Families retain a separate source value at every parameter under each binder. -/
inductive EnvironmentRelated {Parameter Scalar Tangent : Type u}
    (scalar : ScalarRelation Parameter Scalar Tangent) :
    {context : List Ty} → (Parameter → Environment Scalar context) →
      Target.Environment Scalar Tangent (context.map Ty.derivative) → Prop where
  | nil : EnvironmentRelated scalar (fun _ => .nil) .nil
  | cons {context : List Ty} {ty : Ty}
      {source : Parameter → ty.denote Scalar}
      {target : ty.derivative.denote Scalar Tangent}
      {sourceEnvironment : Parameter → Environment Scalar context}
      {targetEnvironment : Target.Environment Scalar Tangent (context.map Ty.derivative)} :
      ValueRelated scalar ty source target →
      EnvironmentRelated scalar sourceEnvironment targetEnvironment →
      EnvironmentRelated scalar
        (fun parameter => .cons (source parameter) (sourceEnvironment parameter))
        (.cons target targetEnvironment)

theorem variable_related {Parameter Scalar Tangent : Type u}
    (scalar : ScalarRelation Parameter Scalar Tangent)
    {context : List Ty} {ty : Ty} (index : Variable context ty) :
    ∀ {sourceEnvironment : Parameter → Environment Scalar context}
      {targetEnvironment : Target.Environment Scalar Tangent (context.map Ty.derivative)},
      EnvironmentRelated scalar sourceEnvironment targetEnvironment →
      ValueRelated scalar ty
        (fun parameter => index.denote (sourceEnvironment parameter))
        (index.adev.denote targetEnvironment) := by
  induction index with
  | head =>
      intro sourceEnvironment targetEnvironment related
      cases related with
      | cons headRelated _ =>
          simpa [Variable.denote, Variable.adev, Target.Variable.denote] using headRelated
  | tail index induction =>
      intro sourceEnvironment targetEnvironment related
      cases related with
      | cons _ tailRelated =>
          simpa [Variable.denote, Variable.adev, Target.Variable.denote] using
            induction tailRelated

theorem value_related {Parameter Scalar Tangent : Type u}
    (zero : Tangent) (scalar : ScalarRelation Parameter Scalar Tangent)
    (constants : ∀ value, scalar (fun _ => value) (value, zero))
    {context : List Ty} {ty : Ty} (value : Value Scalar context ty) :
    ∀ {sourceEnvironment : Parameter → Environment Scalar context}
      {targetEnvironment : Target.Environment Scalar Tangent (context.map Ty.derivative)},
      EnvironmentRelated scalar sourceEnvironment targetEnvironment →
      ValueRelated scalar ty
        (fun parameter => value.denote (sourceEnvironment parameter))
        ((value.adev zero).denote targetEnvironment) := by
  induction value with
  | var index =>
      intro sourceEnvironment targetEnvironment related
      simpa [Value.denote, Value.adev, Target.Value.denote] using
        variable_related scalar index related
  | unit =>
      intro sourceEnvironment targetEnvironment related
      trivial
  | scalar literal =>
      intro sourceEnvironment targetEnvironment related
      exact constants literal
  | pair left right leftInduction rightInduction =>
      intro sourceEnvironment targetEnvironment related
      exact ⟨leftInduction related, rightInduction related⟩

/-- A computation relation retains the full parameterized source effect.
Different source families with the same value at one point remain distinct. -/
abbrev ComputationRelation (Parameter Scalar Tangent : Type u)
    (Effect : Type u → Type v) (Estimate : Type w) :=
  (result : Ty) → (Parameter → Effect (result.denote Scalar)) →
    ((result.derivative.denote Scalar Tangent → Estimate) → Estimate) → Prop

/-- Family-level composition and primitive obligations for the existing CPS transform.
Primitive fields include their analytic obligations through the selected relations.
No continuous primitive law or differentiation-under-integration theorem is assumed here. -/
structure Certificate {Parameter Scalar Tangent : Type u}
    {Effect : Type u → Type v} {Estimate : Type w}
    (zero : Tangent) (sourceModel : Model Scalar Effect)
    (targetModel : Target.Model Scalar Tangent Estimate)
    (scalar : ScalarRelation Parameter Scalar Tangent)
    (relation : ComputationRelation Parameter Scalar Tangent Effect Estimate) : Prop where
  constants : ∀ value, scalar (fun _ => value) (value, zero)
  pure : {result : Ty} → {source : Parameter → result.denote Scalar} →
    {target : result.derivative.denote Scalar Tangent} →
    ValueRelated scalar result source target →
      relation result (fun parameter => sourceModel.pure (source parameter))
        (fun continuation => continuation target)
  bind : {bound result : Ty} →
    {sourceFirst : Parameter → Effect (bound.denote Scalar)} →
    {targetFirst : (bound.derivative.denote Scalar Tangent → Estimate) → Estimate} →
    {sourceBody : Parameter → bound.denote Scalar → Effect (result.denote Scalar)} →
    {targetBody : bound.derivative.denote Scalar Tangent →
      (result.derivative.denote Scalar Tangent → Estimate) → Estimate} →
    relation bound sourceFirst targetFirst →
    (∀ source target, ValueRelated scalar bound source target →
      relation result (fun parameter => sourceBody parameter (source parameter))
        (targetBody target)) →
    relation result
      (fun parameter => sourceModel.bind (sourceFirst parameter) (sourceBody parameter))
      (fun continuation => targetFirst fun target => targetBody target continuation)
  normalReparameterized : {sourceMean sourceScale : Parameter → Scalar} →
    {targetMean targetScale : Target.Jet Scalar Tangent} →
    scalar sourceMean targetMean → scalar sourceScale targetScale →
    relation .scalar
      (fun parameter => sourceModel.normalReparameterized
        (sourceMean parameter) (sourceScale parameter))
      (targetModel.normalReparameterized targetMean targetScale)
  normalReinforce : {sourceMean sourceScale : Parameter → Scalar} →
    {targetMean targetScale : Target.Jet Scalar Tangent} →
    scalar sourceMean targetMean → scalar sourceScale targetScale →
    relation .scalar
      (fun parameter => sourceModel.normalReinforce
        (sourceMean parameter) (sourceScale parameter))
      (targetModel.normalReinforce targetMean targetScale)

/-- The unchanged source ADEV transform preserves parameterized, seeded relations.
The binder case carries the complete bound family into the continuation. -/
theorem fundamental {Parameter Scalar Tangent : Type u}
    {Effect : Type u → Type v} {Estimate : Type w}
    (zero : Tangent) (sourceModel : Model Scalar Effect)
    (targetModel : Target.Model Scalar Tangent Estimate)
    (scalar : ScalarRelation Parameter Scalar Tangent)
    (relation : ComputationRelation Parameter Scalar Tangent Effect Estimate)
    (certificate : Certificate zero sourceModel targetModel scalar relation)
    {context : List Ty} {result : Ty} (term : Term Scalar context result) :
    ∀ {sourceEnvironment : Parameter → Environment Scalar context}
      {targetEnvironment : Target.Environment Scalar Tangent (context.map Ty.derivative)},
      EnvironmentRelated scalar sourceEnvironment targetEnvironment →
      relation result
        (fun parameter => term.denote sourceModel (sourceEnvironment parameter))
        ((term.adev zero).denote targetModel targetEnvironment) := by
  induction term with
  | pure value =>
      intro sourceEnvironment targetEnvironment related
      exact certificate.pure (value_related zero scalar certificate.constants value related)
  | let_ first body firstInduction bodyInduction =>
      intro sourceEnvironment targetEnvironment related
      apply certificate.bind (firstInduction related)
      intro source target valuesRelated
      exact bodyInduction (.cons valuesRelated related)
  | normalReparameterized mean scale =>
      intro sourceEnvironment targetEnvironment related
      exact certificate.normalReparameterized
        (value_related zero scalar certificate.constants mean related)
        (value_related zero scalar certificate.constants scale related)
  | normalReinforce mean scale =>
      intro sourceEnvironment targetEnvironment related
      exact certificate.normalReinforce
        (value_related zero scalar certificate.constants mean related)
        (value_related zero scalar certificate.constants scale related)

end Problib.Inference.Derivative.Source.Family
