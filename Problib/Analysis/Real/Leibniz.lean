module

public import Problib.Analysis.Real.Dominated
public import Problib.Analysis.Real.Interchange

/-! Differentiation under the integral sign, discharged.

`Problib.Analysis.Real.Interchange` states the exchange of a parameter
derivative with an integral and its dominated premise without proving either.
This module proves the exchange from the premise. The secant of the integral
is the integral of the secants, because certified integrals subtract and scale,
and the punctured form of dominated convergence carries the secants to the
pointwise derivative. The definitions of `Interchange` are used unchanged.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind
open Problib.Measure Problib.Measure.Real

universe u

variable {α : Type u} {space : Space α}

noncomputable section

/-- The secant of a certified family's integral is the certified integral of
the secants of its integrands. -/
public theorem IntegralFamily.secant_hasRealIntegral {measure : Measure space}
    (family : IntegralFamily measure) (parameter displacement : selection.Carrier) :
    HasRealIntegral measure
      (fun point => secant (fun step => family.integrand step point) parameter displacement)
      (secant family.value parameter displacement) := by
  have scaled := ((family.certified (add parameter displacement)).sub
    (family.certified parameter)).smul (inverse displacement)
  have valueEqual : mul (inverse displacement)
      (sub (family.value (add parameter displacement)) (family.value parameter)) =
      secant family.value parameter displacement := by
    rw [secant, div_eq_mul_inverse, mul_comm]
  rw [valueEqual] at scaled
  exact scaled.congr (fun point => by rw [secant, div_eq_mul_inverse, mul_comm])

/-- The Leibniz rule. A family whose difference quotients are dominated at a
parameter, and whose integrands are differentiable there with a measurable
pointwise derivative, differentiates under the integral sign: the pointwise
derivative is integrable and its integral is the derivative of the integral. -/
public theorem differentiatesUnderIntegral_of_dominated {measure : Measure space}
    {family : IntegralFamily measure} {parameter : selection.Carrier}
    {pointwise : α → selection.Carrier}
    (dominated : HasDominatedDifferenceQuotients family parameter)
    (differentiable : HasPointwiseDerivative family parameter pointwise)
    (measurable : MeasurableMap space borel pointwise) :
    ∃ derivative : selection.Carrier,
      DifferentiatesUnderIntegral family parameter pointwise derivative := by
  rcases dominated with
    ⟨radius, dominator, _, radiusPositive, dominatorIntegral, _, bound⟩
  rcases dominated_convergence_approaches
      (family := fun displacement point =>
        secant (fun step => family.integrand step point) parameter displacement)
      (values := secant family.value parameter) radiusPositive
      (fun displacement _ _ => family.secant_hasRealIntegral parameter displacement)
      measurable dominatorIntegral bound differentiable with
    ⟨derivative, integral, approaches⟩
  exact ⟨derivative, differentiable, integral, approaches⟩

/-- The Leibniz rule at a named derivative. When the pointwise derivative's
integral is already certified, its value is the derivative of the integral;
measurability comes from the certificate. -/
public theorem differentiatesUnderIntegral_of_integral {measure : Measure space}
    {family : IntegralFamily measure} {parameter : selection.Carrier}
    {pointwise : α → selection.Carrier} {derivative : selection.Carrier}
    (dominated : HasDominatedDifferenceQuotients family parameter)
    (differentiable : HasPointwiseDerivative family parameter pointwise)
    (integral : HasRealIntegral measure pointwise derivative) :
    DifferentiatesUnderIntegral family parameter pointwise derivative := by
  have measurable : MeasurableMap space borel pointwise := by
    obtain ⟨parts, _⟩ := integral
    intro set measurableSet
    exact parts.measurable measurableSet
  rcases differentiatesUnderIntegral_of_dominated dominated differentiable
      measurable with
    ⟨other, _, otherIntegral, otherDerivative⟩
  rw [HasRealIntegral.unique otherIntegral integral] at otherDerivative
  exact ⟨differentiable, integral, otherDerivative⟩

end

end Problib.Analysis.Real
