module

public import Problib.Analysis.Real.PowerSeries.SubstitutionProduct

/-! Formal degree filtration for power-series substitution. A zero-constant
inner series has no terms below degree one, so its kth finite power starts
at degree k. This makes every coefficient of an outer substitution finite. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind

noncomputable section

@[expose] public def CoefficientsVanishBelow {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (order : Nat) : Prop :=
  ∀ index, MultiIndex.degree dimension index < order →
    coefficients index = zero

private theorem coefficientAt_zero_of_terms {dimension : Nat}
    (terms : List (FinitePolynomial.Term dimension))
    (allZero : ∀ term, term ∈ terms → term.coefficient = zero)
    (index : MultiIndex.carrier dimension) :
    FinitePolynomial.coefficientAt terms index = zero := by
  induction terms with
  | nil => rfl
  | cons term rest induction =>
      have head := allZero term List.mem_cons_self
      have tail : ∀ later, later ∈ rest → later.coefficient = zero :=
        fun later member => allZero later
          (List.mem_cons_of_mem term member)
      simp only [FinitePolynomial.coefficientAt, List.foldr_cons,
        head]
      rw [← FinitePolynomial.coefficientAt, induction tail]
      split <;> rw [zero_add]

private theorem shellTerms_zero_below {dimension degreeValue order : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (vanish : CoefficientsVanishBelow coefficients order)
    (below : degreeValue < order) :
    ∀ term, term ∈ shellTerms coefficients degreeValue →
      term.coefficient = zero := by
  intro term member
  rcases List.mem_map.mp member with ⟨index, indexMember, equal⟩
  subst term
  have indexBelow : MultiIndex.degree dimension index < order := by
    rw [MultiIndex.degree_of_mem_shell indexMember]
    exact below
  exact vanish index indexBelow

private theorem product_terms_zero_below
    {dimension firstOrder secondOrder degreeValue : Nat}
    (first second : MultiIndex.carrier dimension → selection.Carrier)
    (firstVanish : CoefficientsVanishBelow first firstOrder)
    (secondVanish : CoefficientsVanishBelow second secondOrder)
    (below : degreeValue < firstOrder + secondOrder) :
    ∀ term, term ∈ rawProductTerms first second degreeValue →
      term.coefficient = zero := by
  intro term member
  rcases List.mem_flatMap.mp member with
    ⟨firstDegree, degreeMember, productMember⟩
  have firstLe : firstDegree ≤ degreeValue := by
    have := List.mem_range.mp degreeMember
    omega
  rcases List.mem_flatMap.mp productMember with
    ⟨left, leftMember, mappedMember⟩
  rcases List.mem_map.mp mappedMember with
    ⟨right, secondMember, equal⟩
  subst term
  change mul left.coefficient right.coefficient = zero
  by_cases firstBelow : firstDegree < firstOrder
  · rw [shellTerms_zero_below first firstVanish firstBelow
      left leftMember, zero_mul]
  · have secondBelow : degreeValue - firstDegree < secondOrder := by
      omega
    rw [shellTerms_zero_below second secondVanish secondBelow
      right secondMember, mul_zero]

public theorem multiplySeriesWithin_order
    {dimension firstOrder secondOrder : Nat}
    (first second : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (belowFirst : le radius first.radius)
    (belowSecond : le radius second.radius)
    (firstVanish : CoefficientsVanishBelow first.coefficients firstOrder)
    (secondVanish : CoefficientsVanishBelow second.coefficients secondOrder) :
    CoefficientsVanishBelow
      (multiplySeriesWithin first second radius positive belowFirst
        belowSecond).coefficients (firstOrder + secondOrder) := by
  intro index below
  change FinitePolynomial.coefficientAt
    (rawProductTerms first.coefficients second.coefficients
      (MultiIndex.degree dimension index)) index = zero
  exact coefficientAt_zero_of_terms _
    (product_terms_zero_below first.coefficients second.coefficients
      firstVanish secondVanish below) index

public theorem seriesPowerWithin_order {dimension : Nat}
    (series : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : le radius series.radius)
    (zeroConstant : series.coefficients
      (MultiIndex.zeroIndex dimension) = zero)
    (count : Nat) :
    CoefficientsVanishBelow
      (seriesPowerWithin series radius positive below count).coefficients
      count := by
  have firstOrder : CoefficientsVanishBelow series.coefficients 1 := by
    intro index indexBelow
    have zeroIndex := MultiIndex.eq_zeroIndex_of_degree_zero
      dimension index (by omega)
    rwa [zeroIndex]
  induction count with
  | zero => intro index belowZero; omega
  | succ count induction =>
      change CoefficientsVanishBelow
        (multiplySeriesWithin
          (seriesPowerWithin series radius positive below count)
          series radius positive
          (by rw [seriesPowerWithin_radius]; exact le_refl radius)
          below).coefficients (count + 1)
      exact multiplySeriesWithin_order _ _ _ _ _ _ induction
        firstOrder

end

end Problib.Analysis.Real.PowerSeries
