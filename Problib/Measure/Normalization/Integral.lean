module

public import Problib.Measure.Normalization
public import Problib.Measure.Integral.Real

/-! Certified integrals against a normalized measure.

Normalizing scales a measure by the reciprocal of its total mass, so a finite
signed integral against the normalized measure is the unnormalized integral
divided by that mass. This is the quotient rule at the level of measures.
-/

set_option autoImplicit false

namespace Problib.Measure

open Problib.Real Problib.Real.Construction.Dedekind Problib.Measure.Real

/-- Normalizing divides a finite signed integral by the total mass. -/
public theorem normalize_hasRealIntegral {β : Type} {carrier : Space β}
    (measure : Measure carrier) (defined : Measure.IsNormalizable measure)
    (integrand : β → Carrier) {numerator : Carrier} {mass : NNReal}
    (total : measure Set.univ = ENNReal.finite mass)
    (integral : HasRealIntegral measure integrand numerator) :
    HasRealIntegral (Measure.normalize measure defined) integrand
      (div numerator mass.toReal) := by
  rw [Measure.normalize_eq_of_total_eq measure defined total]
  have value : mul (NNReal.div NNReal.one mass).toReal numerator =
      div numerator mass.toReal := by
    rw [NNReal.toReal_div, NNReal.toReal_one, div_eq_mul_inverse, mul_comm one (inverse mass.toReal),
      mul_one, mul_comm (inverse mass.toReal) numerator, ← div_eq_mul_inverse]
  rw [← value]
  exact smul_hasRealIntegral measure integrand (NNReal.div NNReal.one mass) integral

end Problib.Measure
