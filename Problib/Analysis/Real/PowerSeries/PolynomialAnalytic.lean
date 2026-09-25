module

public import Problib.Analysis.Real.PowerSeries.Product

/-! Finite polynomials inherit local analytic representations from their
coordinates and the proved series product law. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

@[expose] public def monomialFactors {dimension : Nat}
    (index : MultiIndex.carrier dimension)
    (point : FiniteVector.carrier dimension)
    (coordinates : List (Fin dimension)) : selection.Carrier :=
  coordinates.foldr
    (fun coordinate total => mul
      (power (point coordinate) (index coordinate)) total) one

public theorem monomialFactors_eq (dimension : Nat)
    (index : MultiIndex.carrier dimension)
    (point : FiniteVector.carrier dimension) :
    monomialFactors index point (List.finRange dimension) =
      MultiIndex.monomial dimension index point := by
  induction dimension with
  | zero => rfl
  | succ dimension induction =>
      rw [List.finRange_succ]
      change mul (power (point 0) (index 0))
          ((List.finRange dimension).map Fin.succ |>.foldr
            (fun coordinate total => mul
              (power (point coordinate) (index coordinate)) total) one) =
        mul (power (point 0) (index 0))
          (MultiIndex.monomial dimension
            (fun coordinate => index coordinate.succ)
            (fun coordinate => point coordinate.succ))
      rw [List.foldr_map]
      exact congrArg (mul (power (point 0) (index 0)))
        (induction (fun coordinate => index coordinate.succ)
          (fun coordinate => point coordinate.succ))

public theorem analytic_on_monomialFactors {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    (openRegion : FiniteVector.IsOpen region)
    (index : MultiIndex.carrier dimension)
    (coordinates : List (Fin dimension)) :
    AnalyticOn region
      (fun point => monomialFactors index point coordinates) := by
  induction coordinates with
  | nil =>
      simpa only [monomialFactors, List.foldr_nil] using
        (analytic_on_constant openRegion one)
  | cons coordinate rest induction =>
      have factor := analytic_on_power_coordinate openRegion coordinate
        (index coordinate)
      have product := analytic_on_mul factor induction
      simpa only [monomialFactors, List.foldr_cons] using product

public theorem analytic_on_monomial {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    (openRegion : FiniteVector.IsOpen region)
    (index : MultiIndex.carrier dimension) :
    AnalyticOn region
      (fun point => MultiIndex.monomial dimension index point) := by
  have factors := analytic_on_monomialFactors openRegion index
    (List.finRange dimension)
  simpa only [monomialFactors_eq] using factors

public theorem analytic_on_finite_polynomial {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    (openRegion : FiniteVector.IsOpen region)
    (terms : List (FinitePolynomial.Term dimension)) :
    AnalyticOn region (fun point => FinitePolynomial.evaluate terms point) := by
  induction terms with
  | nil =>
      simpa only [FinitePolynomial.evaluate, List.foldr_nil] using
        (analytic_on_constant openRegion zero)
  | cons term rest induction =>
      have monomial := analytic_on_monomial openRegion term.exponent
      have scaled := analytic_on_scale monomial term.coefficient
      have combined := analytic_on_add scaled induction
      simpa only [FinitePolynomial.evaluate, List.foldr_cons,
        FinitePolynomial.termValue] using combined

end

end Problib.Analysis.Real.PowerSeries
