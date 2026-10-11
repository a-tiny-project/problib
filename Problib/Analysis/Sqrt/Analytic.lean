module

public import Problib.Analysis.Sqrt
public import Problib.Analysis.Exponential.Analytic
public import Problib.Analysis.Logarithm.Analytic

/-! The square root is analytic on the positive reals.

On positive inputs `sqrt x` is `exp (log x / 2)` by its definition, so its
analyticity is the logarithm's and the exponential's, by composition, with no
series of its own.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.PowerSeries
open Logarithm

noncomputable section

/-- The square root of a positive real is `exp (log x / 2)`. -/
public theorem sqrt_ofReal_of_positive {value : selection.Carrier}
    (positive : lt zero value) :
    (sqrt (NNReal.ofReal value)).val = exp (div (logIntegral value) (add one one)) := by
  have lifted : NNReal.lt NNReal.zero (NNReal.ofReal value) := by
    unfold NNReal.lt NNReal.le
    rw [NNReal.toReal_ofReal positive.left]
    exact positive
  rw [sqrt_of_positive _ lifted]
  have inner : (NNReal.ofReal value).val = value := NNReal.toReal_ofReal positive.left
  rw [inner]
  exact NNReal.toReal_ofReal (exp_positive _).left

/-- The square root is analytic on the positive reals. -/
public theorem analytic_on_sqrt :
    AnalyticOn (fun point : FiniteVector.carrier 1 => lt zero (point 0))
      (fun point => (sqrt (NNReal.ofReal (point 0))).val) := by
  have halved : AnalyticOn (fun point : FiniteVector.carrier 1 => lt zero (point 0))
      (fun point => div (logIntegral (point 0)) (add one one)) := by
    refine analytic_on_congr (fun point _ => ?_)
      (analytic_on_scale analytic_on_log (inverse (add one one)))
    rw [div_eq_mul_inverse, mul_comm]
  exact analytic_on_congr (fun _ member => (sqrt_ofReal_of_positive member).symm)
    (analytic_on_exp_comp halved)

end

end Problib.Analysis
