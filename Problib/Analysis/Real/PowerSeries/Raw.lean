module

public import Problib.Analysis.Real.PowerSeries.Aggregate
public import Problib.Analysis.Real.SignedSeries.CauchyProduct

/-! Degreewise finite-term series and their Cauchy products.

Finite term lists make the product a Cartesian product in each degree. The
aggregation theorem converts each homogeneous list to canonical multiindex
coefficients while preserving evaluation and reducing the magnitude bound.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

@[expose] public def shellTerms {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (degreeValue : Nat) : List (FinitePolynomial.Term dimension) :=
  (MultiIndex.degreeShell dimension degreeValue).map fun index =>
    ⟨index, coefficients index⟩

public theorem shellTerms_homogeneous {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (degreeValue : Nat) :
    FinitePolynomial.Homogeneous degreeValue
      (shellTerms coefficients degreeValue) := by
  intro term member
  rcases List.mem_map.mp member with ⟨index, indexMember, equal⟩
  subst term
  exact MultiIndex.degree_of_mem_shell indexMember

public theorem evaluate_shellTerms {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension)
    (degreeValue : Nat) :
    FinitePolynomial.evaluate (shellTerms coefficients degreeValue)
      displacement = shellTerm coefficients displacement degreeValue := by
  unfold FinitePolynomial.evaluate shellTerms shellTerm
  rw [List.foldr_map]
  rfl

public theorem magnitude_shellTerms {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension)
    (degreeValue : Nat) :
    FinitePolynomial.magnitude (shellTerms coefficients degreeValue)
      displacement = shellMagnitude coefficients displacement degreeValue := by
  unfold FinitePolynomial.magnitude shellTerms shellMagnitude
  rw [List.foldr_map]
  rfl

@[expose] public def rawProductTerms {dimension : Nat}
    (first second : MultiIndex.carrier dimension → selection.Carrier)
    (degreeValue : Nat) : List (FinitePolynomial.Term dimension) :=
  (List.range (degreeValue + 1)).flatMap fun firstDegree =>
    FinitePolynomial.multiply (shellTerms first firstDegree)
      (shellTerms second (degreeValue - firstDegree))

public theorem raw_product_homogeneous {dimension : Nat}
    (first second : MultiIndex.carrier dimension → selection.Carrier)
    (degreeValue : Nat) :
    FinitePolynomial.Homogeneous degreeValue
      (rawProductTerms first second degreeValue) := by
  intro term member
  rcases List.mem_flatMap.mp member with
    ⟨firstDegree, degreeMember, termMember⟩
  have included : firstDegree ≤ degreeValue := by
    have := List.mem_range.mp degreeMember
    omega
  have productDegree := FinitePolynomial.homogeneous_multiply
    (shellTerms_homogeneous first firstDegree)
    (shellTerms_homogeneous second (degreeValue - firstDegree))
    term termMember
  have arithmetic : firstDegree + (degreeValue - firstDegree) =
      degreeValue := Nat.add_sub_of_le included
  rwa [arithmetic] at productDegree

private theorem evaluate_flat_map {dimension : Nat}
    (indices : List Nat)
    (terms : Nat → List (FinitePolynomial.Term dimension))
    (displacement : FiniteVector.carrier dimension) :
    FinitePolynomial.evaluate (indices.flatMap terms) displacement =
      indices.foldr
        (fun index total => add
          (FinitePolynomial.evaluate (terms index) displacement) total)
        zero := by
  induction indices with
  | nil => rfl
  | cons index rest induction =>
      rw [List.flatMap_cons, FinitePolynomial.evaluate_append, induction]
      rfl

private theorem magnitude_flat_map {dimension : Nat}
    (indices : List Nat)
    (terms : Nat → List (FinitePolynomial.Term dimension))
    (displacement : FiniteVector.carrier dimension) :
    FinitePolynomial.magnitude (indices.flatMap terms) displacement =
      indices.foldr
        (fun index total => add
          (FinitePolynomial.magnitude (terms index) displacement) total)
        zero := by
  induction indices with
  | nil => rfl
  | cons index rest induction =>
      rw [List.flatMap_cons, FinitePolynomial.magnitude_append, induction]
      rfl

private theorem foldr_sum_init (values : Nat → selection.Carrier)
    (indices : List Nat) (initial : selection.Carrier) :
    indices.foldr (fun index total => add (values index) total) initial =
      add (indices.foldr (fun index total => add (values index) total) zero)
        initial := by
  induction indices with
  | nil => rw [List.foldr_nil, List.foldr_nil, zero_add]
  | cons index rest induction =>
      rw [List.foldr_cons, List.foldr_cons, induction, add_assoc]

private theorem foldr_range_partial_sum (values : Nat → selection.Carrier)
    (count : Nat) :
    (List.range count).foldr
      (fun index total => add (values index) total) zero =
    partialSum values count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.range_succ, List.foldr_append]
      change (List.range count).foldr
        (fun index total => add (values index) total)
        (add (values count) zero) = partialSum values (count + 1)
      rw [add_zero, foldr_sum_init, induction, partial_sum_succ]

public theorem partial_sum_cons (values : Nat → selection.Carrier)
    (count : Nat) :
    partialSum values (count + 1) =
      add (values 0)
        (partialSum (fun index => values (index + 1)) count) := by
  induction count with
  | zero =>
      rw [partial_sum_succ, partial_sum_zero, partial_sum_zero,
        zero_add, add_zero]
  | succ count induction =>
      rw [partial_sum_succ values (count + 1), induction,
        partial_sum_succ (fun index => values (index + 1)) count,
        add_assoc]

@[expose] public def fullShellTerms {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension) :
    Nat → selection.Carrier :=
  fun degreeValue => shellTerm series.coefficients displacement degreeValue

@[expose] public def fullShellMagnitudes {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension) :
    Nat → selection.Carrier :=
  fun degreeValue => shellMagnitude series.coefficients displacement degreeValue

public theorem fullShellMagnitudes_summable {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    Summable (fullShellMagnitudes series displacement) := by
  rcases series.normalOn displacement inside with ⟨upper, bounded⟩
  have upperNonnegative : le zero upper := by
    have atZero := bounded 0
    rwa [partial_sum_zero] at atZero
  have fullNonnegative : ∀ degreeValue,
      le zero (fullShellMagnitudes series displacement degreeValue) :=
    fun degreeValue => shellMagnitude_nonnegative
      series.coefficients displacement degreeValue
  apply summable_of_nonnegative_bounded fullNonnegative
  refine ⟨add (fullShellMagnitudes series displacement 0) upper,
    fun count => ?_⟩
  cases count with
  | zero =>
      rw [partial_sum_zero]
      exact add_nonnegative (fullNonnegative 0) upperNonnegative
  | succ count =>
      rw [partial_sum_cons]
      have shifted :
          (fun index => fullShellMagnitudes series displacement
            (index + 1)) =
          tailMagnitudes series.coefficients displacement := rfl
      rw [shifted]
      exact add_le_add (le_refl _) (bounded count)

public theorem fullShellTerms_absolute {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    AbsolutelySummable (fullShellTerms series displacement) := by
  let magnitudeCertificate :=
    fullShellMagnitudes_summable series displacement inside
  refine ⟨sum (fullShellMagnitudes series displacement)
    magnitudeCertificate, fun count => ?_⟩
  have termBound : ∀ degreeValue,
      le (abs (fullShellTerms series displacement degreeValue))
        (fullShellMagnitudes series displacement degreeValue) :=
    fun degreeValue => abs_shellTerm_le_magnitude
      series.coefficients displacement degreeValue
  exact le_trans (partial_sum_le termBound count)
    (partial_sum_le_sum_nonnegative
      (fun degreeValue => shellMagnitude_nonnegative
        series.coefficients displacement degreeValue)
      magnitudeCertificate count)

private theorem converges_to_of_shift
    {values : Nat → selection.Carrier} {limit : selection.Carrier}
    (shifted : Problib.Analysis.Real.ConvergesTo
      (fun index => values (index + 1)) limit) :
    Problib.Analysis.Real.ConvergesTo values limit := by
  intro tolerance positive
  rcases shifted tolerance positive with ⟨stage, close⟩
  refine ⟨stage + 1, fun index later => ?_⟩
  cases index with
  | zero => omega
  | succ index =>
      exact close index (by omega)

/-- The full degreewise sum is the constant coefficient plus the positive
degree tail used by `value`. -/
public theorem full_shell_sum_eq_value {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    sum (fullShellTerms series displacement)
        (summable_of_absolute_bound
          (fullShellTerms_absolute series displacement inside)) =
      value series displacement inside := by
  let full := fullShellTerms series displacement
  let tail := tailTerms series.coefficients displacement
  let tailCertificate := summable_of_absolute_bound
    (series.absoluteOn displacement inside)
  have shiftedEqual :
      (fun count => partialSum full (count + 1)) =
      (fun count => add (full 0) (partialSum tail count)) := by
    funext count
    have shifted : (fun index => full (index + 1)) = tail := rfl
    rw [partial_sum_cons, shifted]
  have shiftedConverges : Problib.Analysis.Real.ConvergesTo
      (fun count => partialSum full (count + 1))
      (add (full 0) (sum tail tailCertificate)) := by
    rw [shiftedEqual]
    exact converges_to_add (converges_to_const (full 0))
      (partial_sum_converges tail tailCertificate)
  have fullConverges := converges_to_of_shift shiftedConverges
  have total := sum_eq_of_converges full
    (summable_of_absolute_bound
      (fullShellTerms_absolute series displacement inside))
    fullConverges
  change sum full
      (summable_of_absolute_bound
        (fullShellTerms_absolute series displacement inside)) =
    add (series.coefficients (MultiIndex.zeroIndex dimension))
      (sum tail tailCertificate)
  rw [total]
  exact congrArg
    (fun constant => add constant (sum tail tailCertificate))
    (shellTerm_zero_degree series.coefficients displacement)

public theorem evaluate_raw_product {dimension : Nat}
    (first second : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension)
    (degreeValue : Nat) :
    FinitePolynomial.evaluate
        (rawProductTerms first second degreeValue) displacement =
      convolution
        (fun degreeValue => shellTerm first displacement degreeValue)
        (fun degreeValue => shellTerm second displacement degreeValue)
        degreeValue := by
  unfold rawProductTerms convolution
  rw [evaluate_flat_map]
  have termsEqual :
      (fun firstDegree =>
        FinitePolynomial.evaluate
          (FinitePolynomial.multiply
            (shellTerms first firstDegree)
            (shellTerms second (degreeValue - firstDegree)))
          displacement) =
      (fun firstDegree => mul
        (shellTerm first displacement firstDegree)
        (shellTerm second displacement
          (degreeValue - firstDegree))) := by
    funext firstDegree
    rw [FinitePolynomial.evaluate_multiply,
      evaluate_shellTerms, evaluate_shellTerms]
  have foldedEqual := congrArg
    (fun values : Nat → selection.Carrier =>
      (List.range (degreeValue + 1)).foldr
        (fun index total => add (values index) total) zero) termsEqual
  rw [foldedEqual]
  exact foldr_range_partial_sum _ (degreeValue + 1)

public theorem magnitude_raw_product {dimension : Nat}
    (first second : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension)
    (degreeValue : Nat) :
    FinitePolynomial.magnitude
        (rawProductTerms first second degreeValue) displacement =
      convolution
        (fun degreeValue => shellMagnitude first displacement degreeValue)
        (fun degreeValue => shellMagnitude second displacement degreeValue)
        degreeValue := by
  unfold rawProductTerms convolution
  rw [magnitude_flat_map]
  have termsEqual :
      (fun firstDegree =>
        FinitePolynomial.magnitude
          (FinitePolynomial.multiply
            (shellTerms first firstDegree)
            (shellTerms second (degreeValue - firstDegree)))
          displacement) =
      (fun firstDegree => mul
        (shellMagnitude first displacement firstDegree)
        (shellMagnitude second displacement
          (degreeValue - firstDegree))) := by
    funext firstDegree
    rw [FinitePolynomial.magnitude_multiply,
      magnitude_shellTerms, magnitude_shellTerms]
  have foldedEqual := congrArg
    (fun values : Nat → selection.Carrier =>
      (List.range (degreeValue + 1)).foldr
        (fun index total => add (values index) total) zero) termsEqual
  rw [foldedEqual]
  exact foldr_range_partial_sum _ (degreeValue + 1)

end

end Problib.Analysis.Real.PowerSeries
