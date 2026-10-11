module

public import Problib.Analysis.Real.Directional
public import Problib.Analysis.Real.Sided
public import Problib.Measure.Integral.Real

/-! Differentiation under the integral sign, stated.

Every score-function or reparameterization estimator rests on exchanging a
parameter derivative with an integral. That exchange is an analytic obligation
with a premise, not an identity, and this module names both so a consumer can
carry them as hypotheses. `Problib.Analysis.Real.Leibniz` derives the
conclusion from the premise. Nothing here is proved:
`DifferentiatesUnderIntegral` is the conclusion an estimator needs, and
`HasDominatedDifferenceQuotients` is the premise that dominated convergence
consumes. The integral is the certified finite signed integral of
`Problib.Measure.Integral.Real`, so an integrand with no integral has no
statement here rather than a conventional value.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind Problib.Measure
open Problib.Measure.Real

universe u

variable {α : Type u} {space : Space α}

noncomputable section

/-- A parameter-indexed integrand whose integral is certified at every
parameter. The value function is what a derivative is taken of. -/
public structure IntegralFamily {α : Type u} {space : Space α}
    (measure : Measure space) where
  /-- The integrand, read at a parameter and a point. -/
  integrand : selection.Carrier → α → selection.Carrier
  /-- The integral of the integrand at each parameter. -/
  value : selection.Carrier → selection.Carrier
  /-- Every parameter's integral is certified, so `value` is not a convention. -/
  certified : ∀ parameter : selection.Carrier,
    HasRealIntegral measure (integrand parameter) (value parameter)

/-- Each point's integrand is differentiable in the parameter, with the stated
pointwise derivative. -/
@[expose] public def HasPointwiseDerivative {measure : Measure space}
    (family : IntegralFamily measure) (parameter : selection.Carrier)
    (pointwise : α → selection.Carrier) (side : Side := .two) : Prop :=
  ∀ point : α,
    HasDerivativeOn side (fun step => family.integrand step point) parameter
      (pointwise point)

/-- Differentiation under the integral sign: the derivative of the integral at
`parameter` is the integral of the pointwise derivative. This is the conclusion
an estimator consumes, and it is a hypothesis until a dominated-convergence
argument supplies it. -/
@[expose] public def DifferentiatesUnderIntegral {measure : Measure space}
    (family : IntegralFamily measure) (parameter : selection.Carrier)
    (pointwise : α → selection.Carrier) (derivative : selection.Carrier)
    (side : Side := .two) : Prop :=
  HasPointwiseDerivative family parameter pointwise side ∧
    HasRealIntegral measure pointwise derivative ∧
      HasDerivativeOn side family.value parameter derivative

/-- The dominated difference quotient premise: one integrable bound, chosen
before the displacement, dominates every secant of every point on a punctured
neighborhood of the parameter. -/
@[expose] public def HasDominatedDifferenceQuotients {measure : Measure space}
    (family : IntegralFamily measure) (parameter : selection.Carrier)
    (side : Side := .two) : Prop :=
  ∃ radius : selection.Carrier, ∃ dominator : α → selection.Carrier,
    ∃ dominatorValue : selection.Carrier,
      lt zero radius ∧
        HasRealIntegral measure dominator dominatorValue ∧
          (∀ point : α, le zero (dominator point)) ∧
            ∀ displacement : selection.Carrier, displacement ≠ zero →
              lt (abs displacement) radius →
                ∀ point : α,
                  le (abs (secant (fun step => family.integrand step point)
                      parameter (side.along displacement)))
                    (dominator point)

end

end Problib.Analysis.Real
