module

public import Problib.Analysis.Gaussian.Cdf
public import Problib.Analysis.Exponential.Analytic
public import Problib.Analysis.Real.PowerSeries.Antiderivative
public import Problib.Analysis.Real.PowerSeries.Product
import Problib.Real.Grind

/-! The standard Gaussian distribution function is analytic on the whole line.

Its derivative, the standard density `exp (-x²/2) / √(2π)`, is the exponential
of a polynomial times a constant, so it is analytic everywhere. At each center
the density's local series is integrated term by term
(`analytic_on_of_hasDerivative`), and the integrated series agrees with the
distribution function because both differentiate to the density and agree at
the center.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.PowerSeries

noncomputable section

/-- The standard density is analytic on the whole line. -/
public theorem analytic_on_density_standard :
    AnalyticOn (fun _ : FiniteVector.carrier 1 => True)
      (fun point => (density zero one (point 0)).toReal) := by
  have formula : (fun point : FiniteVector.carrier 1 => (density zero one (point 0)).toReal) =
      fun point => mul
        (exp (mul (neg (inverse (selection.ofRat 2))) (mul (point 0) (point 0))))
        (inverse (normalizer one).toReal) := by
    funext point
    rw [density_toReal, mul_one, sub_zero, div_eq_mul_inverse, div_eq_mul_inverse,
      mul_comm (mul (point 0) (point 0)), neg_mul]
  rw [formula]
  have coordinate := analytic_on_coordinate (FiniteVector.is_open_univ 1) 0
  exact analytic_on_mul
    (analytic_on_exp_comp (analytic_on_mul
      (analytic_on_constant (FiniteVector.is_open_univ 1) (neg (inverse (selection.ofRat 2))))
      (analytic_on_mul coordinate coordinate)))
    (analytic_on_constant (FiniteVector.is_open_univ 1) (inverse (normalizer one).toReal))

/-- The standard Gaussian distribution function is analytic on the whole line. -/
public theorem analytic_on_cdf :
    AnalyticOn (fun _ : FiniteVector.carrier 1 => True) (fun point => cdf (point 0)) :=
  analytic_on_of_hasDerivative (derivative := fun value => (density zero one value).toReal)
    analytic_on_density_standard (fun point _ => hasDerivative_cdf (point 0))

/-- The distribution function of an analytic function is analytic. -/
public theorem analytic_on_cdf_comp {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function) :
    AnalyticOn region (fun point => cdf (function point)) :=
  analytic_on_comp (inner := fun point _ => function point)
    analytic.left (fun _ => analytic) analytic_on_cdf (fun _ _ => True.intro)

end

end Problib.Analysis.Gaussian
