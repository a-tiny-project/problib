module

public import Problib.Analysis.Real.PowerSeries.DerivativeCoefficients

/-! Algebraic coefficients of repeated coordinate derivatives. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) mul :=
  ⟨mul_comm⟩

@[expose] public def derivativeCountIndex {dimension : Nat} :
    List (Fin dimension) → MultiIndex.carrier dimension
  | [] => MultiIndex.zeroIndex dimension
  | selected :: rest =>
      MultiIndex.addIndex (derivativeCountIndex rest)
        (MultiIndex.unitIndex selected)

public theorem derivativeCountIndex_eq_count {dimension : Nat}
    (steps : List (Fin dimension)) (coordinate : Fin dimension) :
    derivativeCountIndex steps coordinate = steps.count coordinate := by
  induction steps with
  | nil => rfl
  | cons selected rest induction =>
      simp only [derivativeCountIndex, MultiIndex.addIndex,
        MultiIndex.unitIndex, List.count_cons, induction]
      by_cases equal : coordinate = selected
      · subst coordinate
        simp
      · simp [equal, Ne.symm equal]

@[expose] public def canonicalDerivativeSteps {dimension : Nat}
    (index : MultiIndex.carrier dimension) : List (Fin dimension) :=
  (List.finRange dimension).flatMap fun coordinate =>
    List.replicate (index coordinate) coordinate

private theorem count_flatmap_replicate {dimension : Nat}
    (values : List (Fin dimension))
    (nodup : values.Nodup)
    (multiplicity : Fin dimension → Nat)
    (selected : Fin dimension) :
    (values.flatMap fun coordinate =>
      List.replicate (multiplicity coordinate) coordinate).count selected =
    if selected ∈ values then multiplicity selected else 0 := by
  induction values with
  | nil => simp
  | cons first rest induction =>
      have firstNotRest := List.nodup_cons.mp nodup |>.1
      have restNodup := List.nodup_cons.mp nodup |>.2
      by_cases same : first = selected
      · subst first
        simp [List.flatMap_cons, List.count_append,
          List.count_replicate_self, induction restNodup,
          firstNotRest]
      · have reverse : selected ≠ first := Ne.symm same
        simp [List.flatMap_cons, List.count_append,
          List.count_replicate, same, reverse,
          induction restNodup]

public theorem derivative_count_canonical {dimension : Nat}
    (index : MultiIndex.carrier dimension) :
    derivativeCountIndex (canonicalDerivativeSteps index) = index := by
  funext coordinate
  rw [derivativeCountIndex_eq_count]
  unfold canonicalDerivativeSteps
  rw [count_flatmap_replicate (List.finRange dimension)
    (Relation.List.finRange_nodup dimension) index coordinate]
  simp [List.mem_finRange]

@[expose] public def derivativeFactor {dimension : Nat} :
    List (Fin dimension) → MultiIndex.carrier dimension →
      selection.Carrier
  | [], _ => one
  | selected :: rest, index =>
      mul (derivativeFactor rest index)
        (naturalScale
          (MultiIndex.addIndex index (derivativeCountIndex rest)
            selected + 1))

@[expose] public noncomputable def iteratedPartialSeries {dimension : Nat}
    (series : Convergent dimension) :
    List (Fin dimension) → Convergent dimension
  | [] => series
  | selected :: rest =>
      iteratedPartialSeries (partialDerivativeSeries series selected) rest

private theorem addIndex_zero_right {dimension : Nat}
    (index : MultiIndex.carrier dimension) :
    MultiIndex.addIndex index (MultiIndex.zeroIndex dimension) = index := by
  funext coordinate
  simp [MultiIndex.addIndex, MultiIndex.zeroIndex]

private theorem addIndex_assoc {dimension : Nat}
    (first second third : MultiIndex.carrier dimension) :
    MultiIndex.addIndex (MultiIndex.addIndex first second) third =
      MultiIndex.addIndex first (MultiIndex.addIndex second third) := by
  funext coordinate
  simp [MultiIndex.addIndex, Nat.add_assoc]

public theorem iterated_partial_coefficients {dimension : Nat}
    (series : Convergent dimension)
    (steps : List (Fin dimension))
    (index : MultiIndex.carrier dimension) :
    (iteratedPartialSeries series steps).coefficients index =
      mul (derivativeFactor steps index)
        (series.coefficients
          (MultiIndex.addIndex index (derivativeCountIndex steps))) := by
  induction steps generalizing series with
  | nil =>
      simp only [iteratedPartialSeries, derivativeFactor,
        derivativeCountIndex, addIndex_zero_right, one_mul]
  | cons selected rest induction =>
      change
        (iteratedPartialSeries
          (partialDerivativeSeries series selected) rest).coefficients
            index = _
      rw [induction (partialDerivativeSeries series selected)]
      change
        mul (derivativeFactor rest index)
          (mul
            (naturalScale
              ((MultiIndex.addIndex index (derivativeCountIndex rest))
                selected + 1))
            (series.coefficients
              (MultiIndex.addIndex
                (MultiIndex.addIndex index (derivativeCountIndex rest))
                (MultiIndex.unitIndex selected)))) =
          mul
            (mul (derivativeFactor rest index)
              (naturalScale
                ((MultiIndex.addIndex index (derivativeCountIndex rest))
                  selected + 1)))
            (series.coefficients
              (MultiIndex.addIndex index
                (MultiIndex.addIndex (derivativeCountIndex rest)
                  (MultiIndex.unitIndex selected))))
      rw [addIndex_assoc]
      ac_rfl

private theorem addIndex_zero_left {dimension : Nat}
    (index : MultiIndex.carrier dimension) :
    MultiIndex.addIndex (MultiIndex.zeroIndex dimension) index = index := by
  funext coordinate
  simp [MultiIndex.addIndex, MultiIndex.zeroIndex]

@[expose] public def multiFactorial {dimension : Nat}
    (index : MultiIndex.carrier dimension) : selection.Carrier :=
  derivativeFactor (canonicalDerivativeSteps index)
    (MultiIndex.zeroIndex dimension)

public theorem naturalScale_succ_positive (count : Nat) :
    lt zero (naturalScale (count + 1)) := by
  change lt zero (add one (naturalScale count))
  have shifted := add_lt_add_left
    (naturalScale count) one_positive
  rw [add_zero, add_comm] at shifted
  exact lt_of_le_of_lt (naturalScale_nonnegative count) shifted

public theorem derivativeFactor_positive {dimension : Nat}
    (steps : List (Fin dimension))
    (index : MultiIndex.carrier dimension) :
    lt zero (derivativeFactor steps index) := by
  induction steps with
  | nil => exact one_positive
  | cons selected rest induction =>
      change lt zero
        (mul (derivativeFactor rest index)
          (naturalScale
            (MultiIndex.addIndex index (derivativeCountIndex rest)
              selected + 1)))
      exact mul_positive induction (naturalScale_succ_positive _)

public theorem multiFactorial_positive {dimension : Nat}
    (index : MultiIndex.carrier dimension) :
    lt zero (multiFactorial index) :=
  derivativeFactor_positive (canonicalDerivativeSteps index)
    (MultiIndex.zeroIndex dimension)

/-- The coefficient at a multiindex is its canonical repeated coordinate
derivative at the center, normalized by its nonzero multiindex factor. -/
public theorem taylor_coefficient_of_iterated_partial {dimension : Nat}
    (series : Convergent dimension)
    (index : MultiIndex.carrier dimension) :
    series.coefficients index =
      div
        ((iteratedPartialSeries series
          (canonicalDerivativeSteps index)).coefficients
          (MultiIndex.zeroIndex dimension))
        (multiFactorial index) := by
  have coefficient := iterated_partial_coefficients series
    (canonicalDerivativeSteps index) (MultiIndex.zeroIndex dimension)
  rw [derivative_count_canonical, addIndex_zero_left] at coefficient
  rw [coefficient]
  change series.coefficients index =
    div (mul (multiFactorial index) (series.coefficients index))
      (multiFactorial index)
  rw [mul_comm (multiFactorial index) (series.coefficients index),
    div_eq_mul_inverse, mul_assoc,
    mul_inverse_cancel
      (nonzero_of_positive (multiFactorial_positive index)),
    mul_one]

public theorem shellTerm_zero_at_origin {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (degreeValue : Nat) (positive : 0 < degreeValue) :
    shellTerm coefficients (FiniteVector.zeroVector dimension)
      degreeValue = zero := by
  unfold shellTerm
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      (∀ index, index ∈ indices →
        MultiIndex.degree dimension index = degreeValue) →
      indices.foldr
        (fun index total => add
          (mul (coefficients index)
            (MultiIndex.monomial dimension index
              (FiniteVector.zeroVector dimension))) total) zero = zero := by
    intro indices
    induction indices with
    | nil => intro _; rfl
    | cons index rest induction =>
        intro homogeneous
        have degree := homogeneous index List.mem_cons_self
        have vanished := MultiIndex.monomial_zero_of_positive_degree
          dimension index (by omega)
        simp only [List.foldr_cons, vanished, mul_zero, zero_add]
        exact induction (fun later member => homogeneous later
          (List.mem_cons_of_mem index member))
  exact go (MultiIndex.degreeShell dimension degreeValue)
    (fun index member => MultiIndex.degree_of_mem_shell member)

public theorem value_at_origin {dimension : Nat}
    (series : Convergent dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius (FiniteVector.zeroVector dimension)) :
    value series (FiniteVector.zeroVector dimension) inside =
      series.coefficients (MultiIndex.zeroIndex dimension) := by
  let terms := tailTerms series.coefficients
    (FiniteVector.zeroVector dimension)
  have termsZero : terms = fun _ : Nat => zero := by
    funext degreeValue
    exact shellTerm_zero_at_origin series.coefficients
      (degreeValue + 1) (by omega)
  have partialZero : ∀ count, partialSum terms count = zero := by
    intro count
    induction count with
    | zero => rfl
    | succ count induction =>
        rw [partial_sum_succ, induction]
        have zeroTerm : terms count = zero := congrFun termsZero count
        rw [zeroTerm, zero_add]
  have converges : Problib.Analysis.Real.ConvergesTo
      (partialSum terms) zero := by
    have equal : partialSum terms = fun _ : Nat => zero := by
      funext count
      exact partialZero count
    rw [equal]
    exact converges_to_const zero
  have total := sum_eq_of_converges terms
    (summable_of_absolute_bound (series.absoluteOn _ inside)) converges
  unfold value
  rw [total, add_zero]

end

end Problib.Analysis.Real.PowerSeries
