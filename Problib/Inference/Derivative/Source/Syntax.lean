set_option autoImplicit false

namespace Problib.Inference.Derivative.Source

universe u v

/-- The first-order source types needed by the published ADEV rules. -/
inductive Ty where
  | unit
  | scalar
  | product (left right : Ty)
  deriving DecidableEq, Repr

namespace Target

/-- ADEV separates primal scalars from tangent values in the target language. -/
inductive Ty where
  | unit
  | scalar
  | tangent
  | product (left right : Ty)
  deriving DecidableEq, Repr

end Target

/-- Forward ADEV's type translation. -/
def Ty.derivative : Ty → Target.Ty
  | .unit => .unit
  | .scalar => .product .scalar .tangent
  | .product left right => .product left.derivative right.derivative

/-- Intrinsically typed de Bruijn variables for the source language. -/
inductive Variable : List Ty → Ty → Type where
  | head {context : List Ty} {ty : Ty} : Variable (ty :: context) ty
  | tail {context : List Ty} {ty other : Ty} :
      Variable context ty → Variable (other :: context) ty

/-- Pure, intrinsically typed source values. -/
inductive Value (Scalar : Type u) : List Ty → Ty → Type u where
  | var {context : List Ty} {ty : Ty} :
      Variable context ty → Value Scalar context ty
  | unit {context : List Ty} : Value Scalar context .unit
  | scalar {context : List Ty} : Scalar → Value Scalar context .scalar
  | pair {context : List Ty} {left right : Ty} :
      Value Scalar context left → Value Scalar context right →
      Value Scalar context (.product left right)

/-- The ordered first-order source computation fragment.

`let_` is the sole composition form. Its order is syntactic and the calculus
contains no exchange or commutativity rule. The two normal constructors retain
the estimator choice made by the source program. -/
inductive Term (Scalar : Type u) : List Ty → Ty → Type u where
  | pure {context : List Ty} {result : Ty} :
      Value Scalar context result → Term Scalar context result
  | let_ {context : List Ty} {bound result : Ty} :
      Term Scalar context bound → Term Scalar (bound :: context) result →
      Term Scalar context result
  | normalReparameterized {context : List Ty} :
      Value Scalar context .scalar → Value Scalar context .scalar →
      Term Scalar context .scalar
  | normalReinforce {context : List Ty} :
      Value Scalar context .scalar → Value Scalar context .scalar →
      Term Scalar context .scalar

namespace Target

/-- Intrinsically typed variables after ADEV's type translation. -/
inductive Variable : List Ty → Ty → Type where
  | head {context : List Ty} {ty : Ty} : Variable (ty :: context) ty
  | tail {context : List Ty} {ty other : Ty} :
      Variable context ty → Variable (other :: context) ty

/-- Pure values in the ADEV target. Scalar and tangent carriers are independent. -/
inductive Value (Scalar : Type u) (Tangent : Type v) : List Ty → Ty → Type (max u v) where
  | var {context : List Ty} {ty : Ty} :
      Variable context ty → Value Scalar Tangent context ty
  | unit {context : List Ty} : Value Scalar Tangent context .unit
  | scalar {context : List Ty} : Scalar → Value Scalar Tangent context .scalar
  | tangent {context : List Ty} : Tangent → Value Scalar Tangent context .tangent
  | pair {context : List Ty} {left right : Ty} :
      Value Scalar Tangent context left → Value Scalar Tangent context right →
      Value Scalar Tangent context (.product left right)

/-- The typed CPS target of the source ADEV transformation.

The normal constructors have the full continuation shape of the published
reparameterization and REINFORCE rules. Their analytic implementations and
correctness obligations are supplied later by a primitive model and its
certificate. -/
inductive CPS (Scalar : Type u) (Tangent : Type v) :
    List Ty → Problib.Inference.Derivative.Source.Ty → Type (max u v) where
  | pure {context : List Ty} {result : Problib.Inference.Derivative.Source.Ty} :
      Value Scalar Tangent context result.derivative →
      CPS Scalar Tangent context result
  | let_ {context : List Ty} {bound result : Problib.Inference.Derivative.Source.Ty} :
      CPS Scalar Tangent context bound →
      CPS Scalar Tangent (bound.derivative :: context) result →
      CPS Scalar Tangent context result
  | normalReparameterized {context : List Ty} :
      Value Scalar Tangent context Problib.Inference.Derivative.Source.Ty.scalar.derivative →
      Value Scalar Tangent context Problib.Inference.Derivative.Source.Ty.scalar.derivative →
      CPS Scalar Tangent context .scalar
  | normalReinforce {context : List Ty} :
      Value Scalar Tangent context Problib.Inference.Derivative.Source.Ty.scalar.derivative →
      Value Scalar Tangent context Problib.Inference.Derivative.Source.Ty.scalar.derivative →
      CPS Scalar Tangent context .scalar

end Target

def Variable.adev : {context : List Ty} → {ty : Ty} → Variable context ty →
    Target.Variable (context.map Ty.derivative) ty.derivative
  | _, _, .head => .head
  | _, _, .tail index => .tail index.adev

/-- Pure-value translation. `zero` is the only tangent operation needed by
this structural fragment. -/
def Value.adev {Scalar : Type u} {Tangent : Type v} (zero : Tangent) :
    {context : List Ty} → {ty : Ty} →
    Value Scalar context ty →
      Target.Value Scalar Tangent (context.map Ty.derivative) ty.derivative
  | _, _, .var index => .var index.adev
  | _, _, .unit => .unit
  | _, _, .scalar value => .pair (.scalar value) (.tangent zero)
  | _, _, .pair left right => .pair (left.adev zero) (right.adev zero)

/-- The published first-order CPS ADEV transformation. -/
def Term.adev {Scalar : Type u} {Tangent : Type v} (zero : Tangent) :
    {context : List Ty} → {result : Ty} →
    Term Scalar context result →
      Target.CPS Scalar Tangent (context.map Ty.derivative) result
  | _, _, .pure value => .pure (value.adev zero)
  | _, _, .let_ first body => .let_ (first.adev zero) (body.adev zero)
  | _, _, .normalReparameterized mean scale =>
      .normalReparameterized (mean.adev zero) (scale.adev zero)
  | _, _, .normalReinforce mean scale =>
      .normalReinforce (mean.adev zero) (scale.adev zero)

@[simp] theorem Term.adev_pure {Scalar : Type u} {Tangent : Type v}
    {context : List Ty} {result : Ty} (zero : Tangent)
    (value : Value Scalar context result) :
    (Term.pure value).adev zero = Target.CPS.pure (value.adev zero) :=
  rfl

@[simp] theorem Term.adev_let {Scalar : Type u} {Tangent : Type v}
    {context : List Ty} {bound result : Ty}
    (zero : Tangent) (first : Term Scalar context bound)
    (body : Term Scalar (bound :: context) result) :
    (Term.let_ first body).adev zero =
      Target.CPS.let_ (first.adev zero) (body.adev zero) :=
  rfl

@[simp] theorem Term.adev_normalReparameterized {Scalar : Type u} {Tangent : Type v}
    {context : List Ty}
    (zero : Tangent) (mean scale : Value Scalar context .scalar) :
    (Term.normalReparameterized mean scale).adev zero =
      Target.CPS.normalReparameterized (mean.adev zero) (scale.adev zero) :=
  rfl

@[simp] theorem Term.adev_normalReinforce {Scalar : Type u} {Tangent : Type v}
    {context : List Ty}
    (zero : Tangent) (mean scale : Value Scalar context .scalar) :
    (Term.normalReinforce mean scale).adev zero =
      Target.CPS.normalReinforce (mean.adev zero) (scale.adev zero) :=
  rfl

end Problib.Inference.Derivative.Source
