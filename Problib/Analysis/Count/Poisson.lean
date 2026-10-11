module

public import Problib.Analysis.Count.Basic
public import Problib.Analysis.Gamma.Conjugate
public import Problib.Analysis.Exponential.Series

/-! The Poisson law on the naturals.

At a rate `λ` the Poisson law gives the count `k` the mass
`λ^k e^(-λ) / k!`, Problib's `Gamma.poissonMass` (`law_singleton`). At a
positive rate the masses sum to one, because `Σ λ^k / k!` is the exponential
series of `λ` (`exp_eq_sum`), so the law is a probability measure
(`law_isProbability`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Count.Poisson

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries (factorialTerm factorial_summable partialSum partialSum_scale
  partialSum_converges)

noncomputable section

/-- The Poisson law: the count `k` has mass `λ^k e^(-λ) / k!`. -/
@[expose] public def law (rate : Carrier) : Measure (Space.discrete Nat) :=
  ofMass (Gamma.poissonMass rate)

/-- The law gives each count its Poisson mass. -/
public theorem law_singleton (rate : Carrier) (count : Nat) :
    law rate (fun value => value = count) = ENNReal.finite (Gamma.poissonMass rate count) :=
  ofMass_singleton _ count

/-- At every rate the Poisson masses, as reals, sum to one. -/
private theorem masses_converge (rate : Carrier) :
    Problib.Analysis.Real.ConvergesTo
      (partialSum fun count => mul (factorialTerm rate count) (exp (neg rate))) one := by
  have scaled := Problib.Analysis.Real.SignedSeries.converges_to_scale (exp (neg rate))
    (partialSum_converges (factorialTerm rate) (factorial_summable rate))
  rw [← exp_eq_sum, exp_neg,
    inverse_mul_cancel (fun vanishing => by
      have positive := exp_positive rate; rw [vanishing] at positive; exact lt_irrefl zero positive)] at scaled
  refine (congrArg (fun values => Problib.Analysis.Real.ConvergesTo values one)
    (funext fun count => ?_)).mp scaled
  rw [← partialSum_scale]
  exact congrArg (partialSum · count) (funext fun index => by rw [exp_neg]; exact mul_comm _ _)

/-- At a nonnegative rate the Poisson law is a probability measure. -/
public theorem law_isProbability {rate : Carrier} (nonnegative : le zero rate) :
    Measure.IsProbability (law rate) :=
  ofMass_isProbability
    (fun count => mul_nonnegative (factorialTerm_nonnegative nonnegative count)
      (exp_positive _).1)
    (masses_converge rate)

end

end Problib.Analysis.Count.Poisson
