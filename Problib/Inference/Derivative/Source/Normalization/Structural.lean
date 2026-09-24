import Problib.Inference.Derivative.Source.Semantics

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source.Normalization.Structural

universe u v w

/-- The only nonstructural clause in the relation between symbolic and
concrete ADEV target values. -/
abbrev TangentRelation (SymbolicTangent ConcreteTangent : Type u) :=
  SymbolicTangent → ConcreteTangent → Prop

/-- The structural relation between two interpretations of an ADEV target
value. Scalars agree exactly. Tangents use the caller's representation
relation. -/
def ValueRelated {Scalar SymbolicTangent ConcreteTangent : Type u}
    (tangentRelated : TangentRelation SymbolicTangent ConcreteTangent) :
    (ty : Target.Ty) → ty.denote Scalar SymbolicTangent →
      ty.denote Scalar ConcreteTangent → Prop
  | .unit, _, _ => True
  | .scalar, symbolic, concrete => symbolic = concrete
  | .tangent, symbolic, concrete => tangentRelated symbolic concrete
  | .product left right, symbolic, concrete =>
      ValueRelated tangentRelated left symbolic.1 concrete.1 ∧
        ValueRelated tangentRelated right symbolic.2 concrete.2

/-- Pointwise structural relation between two ADEV target environments. -/
inductive EnvironmentRelated {Scalar SymbolicTangent ConcreteTangent : Type u}
    (tangentRelated : TangentRelation SymbolicTangent ConcreteTangent) :
    {context : List Target.Ty} →
      Target.Environment Scalar SymbolicTangent context →
      Target.Environment Scalar ConcreteTangent context → Prop where
  | nil : EnvironmentRelated tangentRelated .nil .nil
  | cons {context : List Target.Ty} {ty : Target.Ty}
      {symbolic : ty.denote Scalar SymbolicTangent}
      {concrete : ty.denote Scalar ConcreteTangent}
      {symbolicEnvironment :
        Target.Environment Scalar SymbolicTangent context}
      {concreteEnvironment :
        Target.Environment Scalar ConcreteTangent context} :
      ValueRelated tangentRelated ty symbolic concrete →
      EnvironmentRelated tangentRelated symbolicEnvironment concreteEnvironment →
      EnvironmentRelated tangentRelated
        (.cons symbolic symbolicEnvironment) (.cons concrete concreteEnvironment)

theorem variable_related {Scalar SymbolicTangent ConcreteTangent : Type u}
    {tangentRelated : TangentRelation SymbolicTangent ConcreteTangent}
    {context : List Target.Ty} {ty : Target.Ty}
    (index : Target.Variable context ty) :
    ∀ {symbolicEnvironment :
        Target.Environment Scalar SymbolicTangent context}
      {concreteEnvironment :
        Target.Environment Scalar ConcreteTangent context},
      EnvironmentRelated tangentRelated symbolicEnvironment concreteEnvironment →
      ValueRelated tangentRelated ty
        (index.denote symbolicEnvironment) (index.denote concreteEnvironment) := by
  induction index with
  | head =>
      intro symbolicEnvironment concreteEnvironment related
      cases related with
      | cons headRelated _ =>
          simpa [Target.Variable.denote] using headRelated
  | tail index induction =>
      intro symbolicEnvironment concreteEnvironment related
      cases related with
      | cons _ tailRelated => exact induction tailRelated

/-- Source variables translated with two tangent representations remain
related in related target environments. -/
theorem source_variable_adev_related
    {Scalar SymbolicTangent ConcreteTangent : Type u}
    {tangentRelated : TangentRelation SymbolicTangent ConcreteTangent}
    {context : List Ty} {ty : Ty} (index : Variable context ty) :
    ∀ {symbolicEnvironment : Target.Environment Scalar SymbolicTangent
        (context.map Ty.derivative)}
      {concreteEnvironment : Target.Environment Scalar ConcreteTangent
        (context.map Ty.derivative)},
      EnvironmentRelated tangentRelated symbolicEnvironment concreteEnvironment →
      ValueRelated tangentRelated ty.derivative
        (index.adev.denote symbolicEnvironment)
        (index.adev.denote concreteEnvironment) := by
  intro symbolicEnvironment concreteEnvironment related
  exact variable_related index.adev related

/-- Pure source-value translation is parametric in the tangent
representation. Only the two translated zero tangents need a local relation. -/
theorem source_value_adev_related
    {Scalar SymbolicTangent ConcreteTangent : Type u}
    {tangentRelated : TangentRelation SymbolicTangent ConcreteTangent}
    (symbolicZero : SymbolicTangent) (concreteZero : ConcreteTangent)
    (zerosRelated : tangentRelated symbolicZero concreteZero)
    {context : List Ty} {ty : Ty} (value : Value Scalar context ty) :
    ∀ {symbolicEnvironment : Target.Environment Scalar SymbolicTangent
        (context.map Ty.derivative)}
      {concreteEnvironment : Target.Environment Scalar ConcreteTangent
        (context.map Ty.derivative)},
      EnvironmentRelated tangentRelated symbolicEnvironment concreteEnvironment →
      ValueRelated tangentRelated ty.derivative
        ((value.adev symbolicZero).denote symbolicEnvironment)
        ((value.adev concreteZero).denote concreteEnvironment) := by
  induction value with
  | var index =>
      intro symbolicEnvironment concreteEnvironment related
      simpa [Value.adev, Target.Value.denote] using
        source_variable_adev_related index related
  | unit =>
      intro symbolicEnvironment concreteEnvironment related
      trivial
  | scalar literal =>
      intro symbolicEnvironment concreteEnvironment related
      exact ⟨rfl, zerosRelated⟩
  | pair left right leftInduction rightInduction =>
      intro symbolicEnvironment concreteEnvironment related
      exact ⟨leftInduction related, rightInduction related⟩

/-- A CPS computation relation parameterized only by its terminal observation.
The relation quantifies over related continuations, so ordered CPS composition
is derivable rather than assumed. -/
def ComputationRelated {Scalar SymbolicTangent ConcreteTangent : Type u}
    {SymbolicEstimate : Type v} {ConcreteEstimate : Type w}
    (tangentRelated : TangentRelation SymbolicTangent ConcreteTangent)
    (observation : SymbolicEstimate → ConcreteEstimate → Prop)
    (result : Ty)
    (symbolic :
      (result.derivative.denote Scalar SymbolicTangent → SymbolicEstimate) →
        SymbolicEstimate)
    (concrete :
      (result.derivative.denote Scalar ConcreteTangent → ConcreteEstimate) →
        ConcreteEstimate) : Prop :=
  ∀ symbolicContinuation concreteContinuation,
    (∀ symbolicValue concreteValue,
      ValueRelated tangentRelated result.derivative symbolicValue concreteValue →
      observation (symbolicContinuation symbolicValue)
        (concreteContinuation concreteValue)) →
    observation (symbolic symbolicContinuation)
      (concrete concreteContinuation)

theorem ComputationRelated.pure
    {Scalar SymbolicTangent ConcreteTangent : Type u}
    {SymbolicEstimate : Type v} {ConcreteEstimate : Type w}
    {tangentRelated : TangentRelation SymbolicTangent ConcreteTangent}
    {observation : SymbolicEstimate → ConcreteEstimate → Prop}
    {result : Ty}
    {symbolicValue : result.derivative.denote Scalar SymbolicTangent}
    {concreteValue : result.derivative.denote Scalar ConcreteTangent}
    (related : ValueRelated tangentRelated result.derivative
      symbolicValue concreteValue) :
    ComputationRelated tangentRelated observation result
      (fun continuation => continuation symbolicValue)
      (fun continuation => continuation concreteValue) := by
  intro symbolicContinuation concreteContinuation continuationsRelated
  exact continuationsRelated symbolicValue concreteValue related

/-- Ordered bind is the relational composition of its first computation and
body. No exchange or commutativity premise appears. -/
theorem ComputationRelated.bind
    {Scalar SymbolicTangent ConcreteTangent : Type u}
    {SymbolicEstimate : Type v} {ConcreteEstimate : Type w}
    {tangentRelated : TangentRelation SymbolicTangent ConcreteTangent}
    {observation : SymbolicEstimate → ConcreteEstimate → Prop}
    {bound result : Ty}
    {symbolicFirst :
      (bound.derivative.denote Scalar SymbolicTangent → SymbolicEstimate) →
        SymbolicEstimate}
    {concreteFirst :
      (bound.derivative.denote Scalar ConcreteTangent → ConcreteEstimate) →
        ConcreteEstimate}
    {symbolicBody : bound.derivative.denote Scalar SymbolicTangent →
      (result.derivative.denote Scalar SymbolicTangent → SymbolicEstimate) →
        SymbolicEstimate}
    {concreteBody : bound.derivative.denote Scalar ConcreteTangent →
      (result.derivative.denote Scalar ConcreteTangent → ConcreteEstimate) →
        ConcreteEstimate}
    (first : ComputationRelated tangentRelated observation bound
      symbolicFirst concreteFirst)
    (body : ∀ symbolicValue concreteValue,
      ValueRelated tangentRelated bound.derivative symbolicValue concreteValue →
      ComputationRelated tangentRelated observation result
        (symbolicBody symbolicValue) (concreteBody concreteValue)) :
    ComputationRelated tangentRelated observation result
      (fun continuation =>
        symbolicFirst fun value => symbolicBody value continuation)
      (fun continuation =>
        concreteFirst fun value => concreteBody value continuation) := by
  intro symbolicContinuation concreteContinuation continuationsRelated
  apply first
  intro symbolicValue concreteValue valuesRelated
  exact body symbolicValue concreteValue valuesRelated
    symbolicContinuation concreteContinuation continuationsRelated

/-- Local reconstruction rule for the reparameterized-normal primitive. -/
structure ReparameterizedCertificate
    {Scalar SymbolicTangent ConcreteTangent : Type u}
    {SymbolicEstimate : Type v} {ConcreteEstimate : Type w}
    (symbolicModel : Target.Model Scalar SymbolicTangent SymbolicEstimate)
    (concreteModel : Target.Model Scalar ConcreteTangent ConcreteEstimate)
    (tangentRelated : TangentRelation SymbolicTangent ConcreteTangent)
    (observation : SymbolicEstimate → ConcreteEstimate → Prop) : Prop where
  sound :
    {symbolicMean symbolicScale : Target.Jet Scalar SymbolicTangent} →
    {concreteMean concreteScale : Target.Jet Scalar ConcreteTangent} →
    ValueRelated tangentRelated Ty.scalar.derivative
      symbolicMean concreteMean →
    ValueRelated tangentRelated Ty.scalar.derivative
      symbolicScale concreteScale →
    ComputationRelated tangentRelated observation .scalar
      (symbolicModel.normalReparameterized symbolicMean symbolicScale)
      (concreteModel.normalReparameterized concreteMean concreteScale)

/-- Local reconstruction rule for the score-function normal primitive. -/
structure ReinforceCertificate
    {Scalar SymbolicTangent ConcreteTangent : Type u}
    {SymbolicEstimate : Type v} {ConcreteEstimate : Type w}
    (symbolicModel : Target.Model Scalar SymbolicTangent SymbolicEstimate)
    (concreteModel : Target.Model Scalar ConcreteTangent ConcreteEstimate)
    (tangentRelated : TangentRelation SymbolicTangent ConcreteTangent)
    (observation : SymbolicEstimate → ConcreteEstimate → Prop) : Prop where
  sound :
    {symbolicMean symbolicScale : Target.Jet Scalar SymbolicTangent} →
    {concreteMean concreteScale : Target.Jet Scalar ConcreteTangent} →
    ValueRelated tangentRelated Ty.scalar.derivative
      symbolicMean concreteMean →
    ValueRelated tangentRelated Ty.scalar.derivative
      symbolicScale concreteScale →
    ComputationRelated tangentRelated observation .scalar
      (symbolicModel.normalReinforce symbolicMean symbolicScale)
      (concreteModel.normalReinforce concreteMean concreteScale)

/-- The admitted source fragment for one pair of target interpretations.

Pure terms require no primitive premise. Ordered composition retains the
premises of its two subterms. Each normal form consumes only its corresponding
local primitive rule. -/
inductive Admission
    {Scalar SymbolicTangent ConcreteTangent : Type u}
    {SymbolicEstimate : Type v} {ConcreteEstimate : Type w}
    (symbolicModel : Target.Model Scalar SymbolicTangent SymbolicEstimate)
    (concreteModel : Target.Model Scalar ConcreteTangent ConcreteEstimate)
    (tangentRelated : TangentRelation SymbolicTangent ConcreteTangent)
    (observation : SymbolicEstimate → ConcreteEstimate → Prop) :
    {context : List Ty} → {result : Ty} →
      Term Scalar context result → Prop where
  | pure {context : List Ty} {result : Ty}
      (value : Value Scalar context result) :
      Admission symbolicModel concreteModel tangentRelated observation (.pure value)
  | let_ {context : List Ty} {bound result : Ty}
      (first : Term Scalar context bound)
      (body : Term Scalar (bound :: context) result) :
      Admission symbolicModel concreteModel tangentRelated observation first →
      Admission symbolicModel concreteModel tangentRelated observation body →
      Admission symbolicModel concreteModel tangentRelated observation (.let_ first body)
  | normalReparameterized {context : List Ty}
      (mean scale : Value Scalar context .scalar) :
      ReparameterizedCertificate symbolicModel concreteModel
        tangentRelated observation →
      Admission symbolicModel concreteModel tangentRelated observation
        (.normalReparameterized mean scale)
  | normalReinforce {context : List Ty}
      (mean scale : Value Scalar context .scalar) :
      ReinforceCertificate symbolicModel concreteModel tangentRelated observation →
      Admission symbolicModel concreteModel tangentRelated observation
        (.normalReinforce mean scale)

/-- Structural CPS normalization theorem.

The proof is independent of probability and expectation. Lean checks
termination through structural recursion on the source term. Pure and ordered
bind are derived by the CPS relation. Only primitive continuation preservation
is supplied by a certificate. -/
theorem fundamental
    {Scalar SymbolicTangent ConcreteTangent : Type u}
    {SymbolicEstimate : Type v} {ConcreteEstimate : Type w}
    (symbolicZero : SymbolicTangent) (concreteZero : ConcreteTangent)
    (symbolicModel : Target.Model Scalar SymbolicTangent SymbolicEstimate)
    (concreteModel : Target.Model Scalar ConcreteTangent ConcreteEstimate)
    (tangentRelated : TangentRelation SymbolicTangent ConcreteTangent)
    (observation : SymbolicEstimate → ConcreteEstimate → Prop)
    (zerosRelated : tangentRelated symbolicZero concreteZero)
    {context : List Ty} {result : Ty} (term : Term Scalar context result)
    (admitted : Admission symbolicModel concreteModel tangentRelated observation term) :
    ∀ {symbolicEnvironment : Target.Environment Scalar SymbolicTangent
        (context.map Ty.derivative)}
      {concreteEnvironment : Target.Environment Scalar ConcreteTangent
        (context.map Ty.derivative)},
      EnvironmentRelated tangentRelated symbolicEnvironment concreteEnvironment →
      ComputationRelated tangentRelated observation result
        ((term.adev symbolicZero).denote symbolicModel symbolicEnvironment)
        ((term.adev concreteZero).denote concreteModel concreteEnvironment) := by
  induction admitted with
  | pure value =>
      intro symbolicEnvironment concreteEnvironment environmentsRelated
      exact ComputationRelated.pure
        (source_value_adev_related symbolicZero concreteZero zerosRelated
          value environmentsRelated)
  | let_ first body firstAdmission bodyAdmission firstInduction bodyInduction =>
      intro symbolicEnvironment concreteEnvironment environmentsRelated
      apply ComputationRelated.bind (firstInduction environmentsRelated)
      intro symbolicValue concreteValue valuesRelated
      exact bodyInduction (.cons valuesRelated environmentsRelated)
  | normalReparameterized mean scale certificate =>
      intro symbolicEnvironment concreteEnvironment environmentsRelated
      exact certificate.sound
        (source_value_adev_related symbolicZero concreteZero zerosRelated
          mean environmentsRelated)
        (source_value_adev_related symbolicZero concreteZero zerosRelated
          scale environmentsRelated)
  | normalReinforce mean scale certificate =>
      intro symbolicEnvironment concreteEnvironment environmentsRelated
      exact certificate.sound
        (source_value_adev_related symbolicZero concreteZero zerosRelated
          mean environmentsRelated)
        (source_value_adev_related symbolicZero concreteZero zerosRelated
          scale environmentsRelated)

end Problib.Inference.Derivative.Source.Normalization.Structural
