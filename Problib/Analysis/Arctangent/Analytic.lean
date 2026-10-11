module

public import Problib.Analysis.Arctangent.Function
public import Problib.Analysis.Real.PowerSeries.Antiderivative
public import Problib.Analysis.Real.PowerSeries.Product
import Problib.Real.Grind

/-! The arctangent is analytic on the whole line.

Its derivative `1 / (1 + x²)` is the reciprocal of a polynomial with no real
zero, so it is analytic everywhere, although its series at zero has radius one.
No series is recentered: at each center the derivative's own local series is
integrated term by term (`analytic_on_of_hasDerivative`), and the integrated
series agrees with the arctangent because both differentiate to the same
function and agree at the center.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.PowerSeries

noncomputable section

private theorem analytic_on_kernel :
    AnalyticOn (fun _ : FiniteVector.carrier 1 => True)
      (fun point => inverse (add one (mul (point 0) (point 0)))) := by
  have coordinate := analytic_on_coordinate (FiniteVector.is_open_univ 1) 0
  refine analytic_on_inverse_comp
    (analytic_on_add (analytic_on_constant (FiniteVector.is_open_univ 1) one)
      (analytic_on_mul coordinate coordinate)) (fun point _ => ?_)
  apply nonzero_of_positive
  have square := mul_self_nonnegative (point 0)
  real_grind

/-- The arctangent is analytic on the whole line. -/
public theorem analytic_on_atan :
    AnalyticOn (fun _ : FiniteVector.carrier 1 => True) (fun point => atan (point 0)) :=
  analytic_on_of_hasDerivative (derivative := fun value => inverse (add one (mul value value)))
    analytic_on_kernel (fun point _ => hasDerivative_atan (point 0))

/-- The arctangent of an analytic function is analytic. -/
public theorem analytic_on_atan_comp {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function) :
    AnalyticOn region (fun point => atan (function point)) :=
  analytic_on_comp (inner := fun point _ => function point)
    analytic.left (fun _ => analytic) analytic_on_atan (fun _ _ => True.intro)

end

end Problib.Analysis
