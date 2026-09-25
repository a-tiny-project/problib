module

public import Problib.Analysis.Real.MultiIndex

/-! Finite homogeneous polynomials as lists of coefficient-monomial terms.

Keeping terms separate makes multiplication a finite Cartesian product. A
later aggregation theorem maps this representation into the canonical
multiindex coefficient family used by convergent power series.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.FinitePolynomial

open Problib.Real.Construction.Dedekind

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) mul :=
  ⟨mul_comm⟩

public structure Term (dimension : Nat) where
  exponent : MultiIndex.carrier dimension
  coefficient : selection.Carrier

@[expose] public def termValue {dimension : Nat} (term : Term dimension)
    (point : FiniteVector.carrier dimension) : selection.Carrier :=
  mul term.coefficient
    (MultiIndex.monomial dimension term.exponent point)

@[expose] public def evaluate {dimension : Nat}
    (terms : List (Term dimension))
    (point : FiniteVector.carrier dimension) : selection.Carrier :=
  terms.foldr (fun term total => add (termValue term point) total) zero

@[expose] public def magnitude {dimension : Nat}
    (terms : List (Term dimension))
    (point : FiniteVector.carrier dimension) : selection.Carrier :=
  terms.foldr (fun term total => add (abs (termValue term point)) total) zero

public theorem magnitude_nonnegative {dimension : Nat}
    (terms : List (Term dimension))
    (point : FiniteVector.carrier dimension) :
    le zero (magnitude terms point) := by
  induction terms with
  | nil => exact le_refl zero
  | cons term rest induction =>
      change le zero
        (add (abs (termValue term point)) (magnitude rest point))
      exact add_nonnegative (abs_nonnegative _) induction

@[expose] public def Homogeneous {dimension : Nat}
    (degreeValue : Nat) (terms : List (Term dimension)) : Prop :=
  ∀ term, term ∈ terms →
    MultiIndex.degree dimension term.exponent = degreeValue

@[expose] public def multiplyTerm {dimension : Nat}
    (first second : Term dimension) : Term dimension where
  exponent := MultiIndex.addIndex first.exponent second.exponent
  coefficient := mul first.coefficient second.coefficient

@[expose] public def multiply {dimension : Nat}
    (first second : List (Term dimension)) : List (Term dimension) :=
  first.flatMap fun left => second.map (multiplyTerm left)

/-- Collect the finite coefficient carried by one multiindex. -/
@[expose] public noncomputable def coefficientAt {dimension : Nat}
    (terms : List (Term dimension))
    (index : MultiIndex.carrier dimension) : selection.Carrier := by
  classical
  exact terms.foldr
    (fun term total =>
      add (if term.exponent = index then term.coefficient else zero) total)
    zero

public theorem termValue_multiply {dimension : Nat}
    (first second : Term dimension)
    (point : FiniteVector.carrier dimension) :
    termValue (multiplyTerm first second) point =
      mul (termValue first point) (termValue second point) := by
  unfold termValue multiplyTerm
  rw [MultiIndex.monomial_addIndex]
  change mul (mul first.coefficient second.coefficient)
      (mul (MultiIndex.monomial dimension first.exponent point)
        (MultiIndex.monomial dimension second.exponent point)) =
    mul (mul first.coefficient
      (MultiIndex.monomial dimension first.exponent point))
      (mul second.coefficient
        (MultiIndex.monomial dimension second.exponent point))
  ac_rfl

public theorem homogeneous_multiply {dimension firstDegree secondDegree : Nat}
    {first second : List (Term dimension)}
    (firstHomogeneous : Homogeneous firstDegree first)
    (secondHomogeneous : Homogeneous secondDegree second) :
    Homogeneous (firstDegree + secondDegree) (multiply first second) := by
  intro term member
  rcases List.mem_flatMap.mp member with
    ⟨left, leftMember, mapped⟩
  rcases List.mem_map.mp mapped with ⟨right, rightMember, equal⟩
  subst term
  change MultiIndex.degree dimension
      (MultiIndex.addIndex left.exponent right.exponent) =
    firstDegree + secondDegree
  rw [MultiIndex.degree_addIndex,
    firstHomogeneous left leftMember,
    secondHomogeneous right rightMember]

public theorem evaluate_append {dimension : Nat}
    (first second : List (Term dimension))
    (point : FiniteVector.carrier dimension) :
    evaluate (first ++ second) point =
      add (evaluate first point) (evaluate second point) := by
  induction first with
  | nil => simp only [List.nil_append, evaluate, List.foldr_nil, zero_add]
  | cons term rest induction =>
      simp only [List.cons_append, evaluate, List.foldr_cons] at *
      rw [induction, add_assoc]

public theorem magnitude_append {dimension : Nat}
    (first second : List (Term dimension))
    (point : FiniteVector.carrier dimension) :
    magnitude (first ++ second) point =
      add (magnitude first point) (magnitude second point) := by
  induction first with
  | nil => simp only [List.nil_append, magnitude, List.foldr_nil, zero_add]
  | cons term rest induction =>
      simp only [List.cons_append, magnitude, List.foldr_cons] at *
      rw [induction, add_assoc]

private theorem evaluate_map_multiply {dimension : Nat}
    (left : Term dimension) (right : List (Term dimension))
    (point : FiniteVector.carrier dimension) :
    evaluate (right.map (multiplyTerm left)) point =
      mul (termValue left point) (evaluate right point) := by
  induction right with
  | nil =>
      change zero = mul (termValue left point) zero
      rw [mul_zero]
  | cons head tail induction =>
      change add (termValue (multiplyTerm left head) point)
          (evaluate (tail.map (multiplyTerm left)) point) =
        mul (termValue left point)
          (add (termValue head point) (evaluate tail point))
      rw [termValue_multiply, induction, mul_add]

private theorem magnitude_map_multiply {dimension : Nat}
    (left : Term dimension) (right : List (Term dimension))
    (point : FiniteVector.carrier dimension) :
    magnitude (right.map (multiplyTerm left)) point =
      mul (abs (termValue left point)) (magnitude right point) := by
  induction right with
  | nil =>
      change zero = mul (abs (termValue left point)) zero
      rw [mul_zero]
  | cons head tail induction =>
      change add (abs (termValue (multiplyTerm left head) point))
          (magnitude (tail.map (multiplyTerm left)) point) =
        mul (abs (termValue left point))
          (add (abs (termValue head point)) (magnitude tail point))
      rw [termValue_multiply, abs_mul, induction, mul_add]

public theorem evaluate_multiply {dimension : Nat}
    (first second : List (Term dimension))
    (point : FiniteVector.carrier dimension) :
    evaluate (multiply first second) point =
      mul (evaluate first point) (evaluate second point) := by
  induction first with
  | nil =>
      change zero = mul zero (evaluate second point)
      rw [zero_mul]
  | cons head tail induction =>
      change evaluate
          ((second.map (multiplyTerm head)) ++ multiply tail second) point =
        mul (add (termValue head point) (evaluate tail point))
          (evaluate second point)
      rw [evaluate_append, evaluate_map_multiply, induction, add_mul]

public theorem magnitude_multiply {dimension : Nat}
    (first second : List (Term dimension))
    (point : FiniteVector.carrier dimension) :
    magnitude (multiply first second) point =
      mul (magnitude first point) (magnitude second point) := by
  induction first with
  | nil =>
      change zero = mul zero (magnitude second point)
      rw [zero_mul]
  | cons head tail induction =>
      change magnitude
          ((second.map (multiplyTerm head)) ++ multiply tail second) point =
        mul (add (abs (termValue head point)) (magnitude tail point))
          (magnitude second point)
      rw [magnitude_append, magnitude_map_multiply, induction, add_mul]

end

end Problib.Analysis.Real.FinitePolynomial
