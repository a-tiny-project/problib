import Problib.Inference.Derivative.Source.Syntax

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source

universe u v

def Ty.denote (Scalar : Type u) : Ty → Type u
  | .unit => PUnit
  | .scalar => Scalar
  | .product left right => left.denote Scalar × right.denote Scalar

/-- A source environment indexed by its typing context. -/
inductive Environment (Scalar : Type u) : List Ty → Type u where
  | nil : Environment Scalar []
  | cons {context : List Ty} {ty : Ty} :
      ty.denote Scalar → Environment Scalar context →
      Environment Scalar (ty :: context)

def Variable.denote {Scalar : Type u} {context : List Ty} {ty : Ty}
    (index : Variable context ty) (environment : Environment Scalar context) :
    ty.denote Scalar :=
  match index, environment with
  | Variable.head, Environment.cons value _ => value
  | Variable.tail rest, Environment.cons _ tailEnvironment =>
      rest.denote tailEnvironment

def Value.denote {Scalar : Type u} {context : List Ty} {ty : Ty}
    (value : Value Scalar context ty) (environment : Environment Scalar context) :
    ty.denote Scalar :=
  match value with
  | Value.var index => index.denote environment
  | Value.unit => PUnit.unit
  | Value.scalar literal => literal
  | Value.pair left right => (left.denote environment, right.denote environment)

/-- An ordered source effect interface. No monad laws or exchange principle are
assumed by the source calculus. -/
structure Model (Scalar : Type u) (Effect : Type u → Type v) where
  pure : {Value : Type u} → Value → Effect Value
  bind : {Left Right : Type u} → Effect Left → (Left → Effect Right) → Effect Right
  normalReparameterized : Scalar → Scalar → Effect Scalar
  normalReinforce : Scalar → Scalar → Effect Scalar

def Term.denote {Scalar : Type u} {Effect : Type u → Type v}
    (model : Model Scalar Effect) {context : List Ty} {result : Ty}
    (term : Term Scalar context result) (environment : Environment Scalar context) :
    Effect (result.denote Scalar) :=
  match term with
  | .pure value => model.pure (value.denote environment)
  | .let_ first body =>
      model.bind (first.denote model environment) fun value =>
        body.denote model (.cons value environment)
  | .normalReparameterized mean scale =>
      model.normalReparameterized (mean.denote environment) (scale.denote environment)
  | .normalReinforce mean scale =>
      model.normalReinforce (mean.denote environment) (scale.denote environment)

namespace Target

def Ty.denote (Scalar Tangent : Type u) : Ty → Type u
  | .unit => PUnit
  | .scalar => Scalar
  | .tangent => Tangent
  | .product left right => left.denote Scalar Tangent × right.denote Scalar Tangent

abbrev Jet (Scalar Tangent : Type u) := Scalar × Tangent

/-- An ADEV-target environment indexed by the translated source context. -/
inductive Environment (Scalar Tangent : Type u) : List Ty → Type u where
  | nil : Environment Scalar Tangent []
  | cons {context : List Ty} {ty : Ty} :
      ty.denote Scalar Tangent → Environment Scalar Tangent context →
      Environment Scalar Tangent (ty :: context)

def Variable.denote {Scalar Tangent : Type u} {context : List Ty} {ty : Ty}
    (index : Variable context ty) (environment : Environment Scalar Tangent context) :
    ty.denote Scalar Tangent :=
  match index, environment with
  | Target.Variable.head, Target.Environment.cons value _ => value
  | Target.Variable.tail rest, Target.Environment.cons _ tailEnvironment =>
      rest.denote tailEnvironment

def Value.denote {Scalar Tangent : Type u} {context : List Ty} {ty : Ty}
    (value : Value Scalar Tangent context ty)
    (environment : Environment Scalar Tangent context) : ty.denote Scalar Tangent :=
  match value with
  | Target.Value.var index => index.denote environment
  | Target.Value.unit => PUnit.unit
  | Target.Value.scalar literal => literal
  | Target.Value.tangent tangentValue => tangentValue
  | Target.Value.pair left right => (left.denote environment, right.denote environment)

/-- Semantics for the two complete CPS primitive rules.

An implementation may expand these operations to the paper's sampling and
score formulas. Correctness is deliberately not bundled here: the fundamental
theorem consumes separate primitive certificates. -/
structure Model (Scalar Tangent : Type u) (Estimate : Type v) where
  normalReparameterized :
    Jet Scalar Tangent → Jet Scalar Tangent →
      (Jet Scalar Tangent → Estimate) → Estimate
  normalReinforce :
    Jet Scalar Tangent → Jet Scalar Tangent →
      (Jet Scalar Tangent → Estimate) → Estimate

/-- CPS interpretation. The `let_` clause preserves source order by nesting
the second computation inside the first continuation. -/
def CPS.denote {Scalar Tangent : Type u} {Estimate : Type v}
    (model : Model Scalar Tangent Estimate) {context : List Ty}
    {result : Problib.Inference.Derivative.Source.Ty}
    (term : CPS Scalar Tangent context result)
    (environment : Environment Scalar Tangent context)
    (continuation : result.derivative.denote Scalar Tangent → Estimate) : Estimate :=
  match term with
  | .pure value => continuation (value.denote environment)
  | .let_ first body =>
      first.denote model environment fun value =>
        body.denote model (.cons value environment) continuation
  | .normalReparameterized mean scale =>
      model.normalReparameterized
        (mean.denote environment) (scale.denote environment) continuation
  | .normalReinforce mean scale =>
      model.normalReinforce
        (mean.denote environment) (scale.denote environment) continuation

end Target

/-- The logical relation for source and translated values. Scalar tangents are
unconstrained, while their primal component must equal the source scalar. -/
def Ty.Related (Scalar Tangent : Type u) :
    (ty : Ty) → ty.denote Scalar → ty.derivative.denote Scalar Tangent → Prop
  | .unit, _, _ => True
  | .scalar, source, target => source = target.1
  | .product left right, source, target =>
      left.Related Scalar Tangent source.1 target.1 ∧
        right.Related Scalar Tangent source.2 target.2

/-- Pointwise logical relation between source and ADEV environments. -/
inductive Environment.Related (Scalar Tangent : Type u) :
    {context : List Ty} → Environment Scalar context →
      Target.Environment Scalar Tangent (context.map Ty.derivative) → Prop where
  | nil : Environment.Related Scalar Tangent .nil .nil
  | cons {context : List Ty} {ty : Ty}
      {source : ty.denote Scalar}
      {target : ty.derivative.denote Scalar Tangent}
      {sourceEnvironment : Environment Scalar context}
      {targetEnvironment :
        Target.Environment Scalar Tangent (context.map Ty.derivative)} :
      ty.Related Scalar Tangent source target →
      Environment.Related Scalar Tangent sourceEnvironment targetEnvironment →
      Environment.Related Scalar Tangent
        (.cons source sourceEnvironment) (.cons target targetEnvironment)

theorem Variable.adev_related {Scalar Tangent : Type u}
    {context : List Ty} {ty : Ty} (index : Variable context ty) :
    ∀ {sourceEnvironment : Environment Scalar context}
      {targetEnvironment : Target.Environment Scalar Tangent (context.map Ty.derivative)},
      Environment.Related Scalar Tangent sourceEnvironment targetEnvironment →
      ty.Related Scalar Tangent (index.denote sourceEnvironment)
        (index.adev.denote targetEnvironment) := by
  induction index with
  | head =>
      intro sourceEnvironment targetEnvironment related
      cases related with
      | cons headRelated _ => simpa [Variable.denote, Variable.adev,
          Target.Variable.denote] using headRelated
  | tail index induction =>
      intro sourceEnvironment targetEnvironment related
      cases related with
      | cons _ tailRelated => exact induction tailRelated

theorem Value.adev_related {Scalar Tangent : Type u} (zero : Tangent)
    {context : List Ty} {ty : Ty} (value : Value Scalar context ty) :
    ∀ {sourceEnvironment : Environment Scalar context}
      {targetEnvironment : Target.Environment Scalar Tangent (context.map Ty.derivative)},
      Environment.Related Scalar Tangent sourceEnvironment targetEnvironment →
      ty.Related Scalar Tangent (value.denote sourceEnvironment)
        ((value.adev zero).denote targetEnvironment) := by
  induction value with
  | var index =>
      intro sourceEnvironment targetEnvironment related
      simpa [Value.denote, Value.adev, Target.Value.denote] using
        index.adev_related related
  | unit =>
      intro sourceEnvironment targetEnvironment related
      trivial
  | scalar literal =>
      intro sourceEnvironment targetEnvironment related
      simp [Value.denote, Value.adev, Target.Value.denote, Ty.Related]
  | pair left right leftInduction rightInduction =>
      intro sourceEnvironment targetEnvironment related
      simpa [Value.denote, Value.adev, Target.Value.denote, Ty.Related] using
        And.intro (leftInduction related) (rightInduction related)

end Problib.Inference.Derivative.Source
