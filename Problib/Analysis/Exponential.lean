module

public import Problib.Analysis.Logarithm.Basic

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Logarithm

noncomputable section

/-- The exponential is the order inverse of the integral logarithm. -/
@[expose] public def exp : Carrier → Carrier := inverseOfOrder logIntegral log_order_data

public theorem exp_positive (x : Carrier) : lt zero (exp x) :=
  inverse_positive logIntegral log_order_data x

public theorem log_exp (x : Carrier) : logIntegral (exp x) = x :=
  inverse_right logIntegral log_order_data x

public theorem exp_log (x : Carrier) (hx : lt zero x) : exp (logIntegral x) = x :=
  inverse_left logIntegral log_order_data hx

public theorem exp_zero : exp zero = one := by
  rw [← log_one]
  exact exp_log one NNReal.one_positive

public theorem exp_add (x y : Carrier) : exp (add x y) = mul (exp x) (exp y) :=
  inverse_add logIntegral log_order_data log_mul x y

public theorem exp_neg (x : Carrier) : exp (neg x) = inverse (exp x) := by
  have h := log_inverse (exp x) (exp_positive x)
  rw [log_exp] at h
  rw [← h]
  exact exp_log _ (inverse_of_positive_positive (exp_positive x))

public theorem exp_monotone : Monotone exp := inverse_monotone logIntegral log_order_data

public theorem exp_strict {x y : Carrier} (hxy : lt x y) : lt (exp x) (exp y) :=
  inverse_strict logIntegral log_order_data hxy

public theorem exp_measurable : MeasurableMap borel borel exp :=
  inverse_measurable logIntegral log_order_data

/-- The positive-domain guard in the logarithm's left inverse is necessary. -/
public theorem exp_log_zero_fails : exp (logIntegral zero) ≠ zero :=
  inverse_left_zero_fails logIntegral log_order_data

end
end Problib.Analysis
