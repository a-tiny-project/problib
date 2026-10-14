module

public import Problib.Analysis.Real.FinitePolynomial
public import Problib.Analysis.Real.PowerSeries

/-! Aggregate a finite homogeneous term list into canonical multiindex
coefficients. Repeated exponents add before evaluation; the triangle inequality
shows aggregation cannot increase the normal-convergence majorant. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind

noncomputable section

public theorem shellTerm_coefficientAt {dimension degreeValue : Nat}
    (terms : List (FinitePolynomial.Term dimension))
    (homogeneous : FinitePolynomial.Homogeneous degreeValue terms)
    (displacement : FiniteVector.carrier dimension) :
    shellTerm (FinitePolynomial.coefficientAt terms)
      displacement degreeValue =
    FinitePolynomial.evaluate terms displacement := by
  induction terms with
  | nil =>
      apply shellTerm_zero_of_coefficients
      intro index _
      rfl
  | cons term rest induction =>
      have termDegree := homogeneous term List.mem_cons_self
      have restHomogeneous :
          FinitePolynomial.Homogeneous degreeValue rest := by
        intro later member
        exact homogeneous later (List.mem_cons_of_mem term member)
      have coefficientsEqual :
          FinitePolynomial.coefficientAt (term :: rest) =
            (fun index => add
              (singleCoefficients term.exponent term.coefficient index)
              (FinitePolynomial.coefficientAt rest index)) := by
        funext index
        simp [FinitePolynomial.coefficientAt, singleCoefficients]
      rw [coefficientsEqual, shellTerm_add,
        shellTerm_single term.exponent term.coefficient displacement
          termDegree,
        induction restHomogeneous]
      rfl

public theorem shellMagnitude_coefficientAt_le
    {dimension degreeValue : Nat}
    (terms : List (FinitePolynomial.Term dimension))
    (homogeneous : FinitePolynomial.Homogeneous degreeValue terms)
    (displacement : FiniteVector.carrier dimension) :
    le (shellMagnitude (FinitePolynomial.coefficientAt terms)
        displacement degreeValue)
      (FinitePolynomial.magnitude terms displacement) := by
  induction terms with
  | nil =>
      have vanished := shellMagnitude_zero_of_coefficients displacement
        (coefficients := FinitePolynomial.coefficientAt [])
        (degreeValue := degreeValue) (fun _ _ => rfl)
      rw [vanished]
      exact le_refl zero
  | cons term rest induction =>
      have termDegree := homogeneous term List.mem_cons_self
      have restHomogeneous :
          FinitePolynomial.Homogeneous degreeValue rest := by
        intro later member
        exact homogeneous later (List.mem_cons_of_mem term member)
      have coefficientsEqual :
          FinitePolynomial.coefficientAt (term :: rest) =
            (fun index => add
              (singleCoefficients term.exponent term.coefficient index)
              (FinitePolynomial.coefficientAt rest index)) := by
        funext index
        simp [FinitePolynomial.coefficientAt, singleCoefficients]
      rw [coefficientsEqual]
      have split := shellMagnitude_add_le
        (singleCoefficients term.exponent term.coefficient)
        (FinitePolynomial.coefficientAt rest) displacement degreeValue
      rw [shellMagnitude_single term.exponent term.coefficient displacement
        termDegree] at split
      have tailBound := induction restHomogeneous
      have combined := add_le_add
        (le_refl (abs (FinitePolynomial.termValue term displacement)))
        tailBound
      change le _
        (add (abs (FinitePolynomial.termValue term displacement))
          (FinitePolynomial.magnitude rest displacement))
      exact le_trans split combined

/-- The coefficient of a multiindex comes from the homogeneous term list at
its own degree. -/
@[expose] public noncomputable def aggregateCoefficients {dimension : Nat}
    (terms : Nat → List (FinitePolynomial.Term dimension)) :
    MultiIndex.carrier dimension → selection.Carrier :=
  fun index => FinitePolynomial.coefficientAt
    (terms (MultiIndex.degree dimension index)) index

public theorem shellTerm_aggregate {dimension degreeValue : Nat}
    (terms : Nat → List (FinitePolynomial.Term dimension))
    (homogeneous : ∀ degreeValue,
      FinitePolynomial.Homogeneous degreeValue (terms degreeValue))
    (displacement : FiniteVector.carrier dimension) :
    shellTerm (aggregateCoefficients terms) displacement degreeValue =
      FinitePolynomial.evaluate (terms degreeValue) displacement := by
  calc
    shellTerm (aggregateCoefficients terms) displacement degreeValue =
      shellTerm (FinitePolynomial.coefficientAt (terms degreeValue))
        displacement degreeValue := by
      apply shellTerm_congr_on
      intro index member
      unfold aggregateCoefficients
      rw [MultiIndex.degree_of_mem_shell member]
    _ = FinitePolynomial.evaluate (terms degreeValue) displacement :=
      shellTerm_coefficientAt (terms degreeValue)
        (homogeneous degreeValue) displacement

public theorem shellMagnitude_aggregate_le {dimension degreeValue : Nat}
    (terms : Nat → List (FinitePolynomial.Term dimension))
    (homogeneous : ∀ degreeValue,
      FinitePolynomial.Homogeneous degreeValue (terms degreeValue))
    (displacement : FiniteVector.carrier dimension) :
    le (shellMagnitude (aggregateCoefficients terms)
        displacement degreeValue)
      (FinitePolynomial.magnitude (terms degreeValue) displacement) := by
  have equal : shellMagnitude (aggregateCoefficients terms)
      displacement degreeValue =
      shellMagnitude (FinitePolynomial.coefficientAt (terms degreeValue))
        displacement degreeValue := by
    apply shellMagnitude_congr_on
    intro index member
    unfold aggregateCoefficients
    rw [MultiIndex.degree_of_mem_shell member]
  rw [equal]
  exact shellMagnitude_coefficientAt_le (terms degreeValue)
    (homogeneous degreeValue) displacement

end

end Problib.Analysis.Real.PowerSeries
