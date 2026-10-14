module

public import Problib.Analysis.Real.Matrix.Algebra
import Problib.Real.Grind

/-! The determinant, by expansion along the first column, and upper triangular
systems.

`det` expands along column 0: row `i` contributes `(-1)^i` times its entry in
column 0 times the determinant of the minor without row `i` and column 0. An
upper triangular matrix has zeros below the diagonal, so its first column is
`(R 0 0, 0, …, 0)`. Its expansion keeps one term, and the minor of that term is
`tail R`, the block left after removing row 0 and column 0. So
`det R = R 0 0 · det (tail R)`. The same split, first coordinate against the
rest, is how product volume adds a coordinate (`volumePi_succ`), which lets the
volume of a triangular image be computed one coordinate at a time.

`solve R y` solves `R x = y` by back substitution in that order: first the
tail system, then the leading coordinate from the first row. When every
diagonal entry is nonzero, it inverts `apply R` on both sides.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.Matrix

open Problib.Real.Construction.Dedekind

noncomputable section

/-- The sign `(-1)^index`. -/
@[expose] public def alternating (index : Nat) : selection.Carrier :=
  if index % 2 = 0 then one else neg one

/-- The index of `Fin (dimension + 1)` that `index` names once `skipped` is
removed. -/
@[expose] public def skipIndex {dimension : Nat} (skipped : Fin (dimension + 1))
    (index : Fin dimension) : Fin (dimension + 1) :=
  if index.val < skipped.val then index.castSucc else index.succ

/-- The matrix without one row and without column 0. -/
@[expose] public def minor {dimension : Nat}
    (matrix : carrier (dimension + 1) (dimension + 1)) (row : Fin (dimension + 1)) :
    carrier dimension dimension :=
  fun other column => matrix (skipIndex row other) column.succ

/-- The matrix without row 0 and column 0. -/
@[expose] public def tail {dimension : Nat} (matrix : carrier (dimension + 1) (dimension + 1)) :
    carrier dimension dimension :=
  fun row column => matrix row.succ column.succ

/-- The determinant, by expansion along the first column. -/
@[expose] public def det : {dimension : Nat} → carrier dimension dimension → selection.Carrier
  | 0, _ => one
  | dimension + 1, matrix => sum (dimension + 1) fun row =>
      mul (alternating row.val) (mul (matrix row 0) (det (minor matrix row)))

/-- Every entry below the diagonal is zero. -/
@[expose] public def UpperTriangular {dimension : Nat} (matrix : carrier dimension dimension) :
    Prop :=
  ∀ row column : Fin dimension, column.val < row.val → matrix row column = zero

public theorem minor_zero {dimension : Nat} (matrix : carrier (dimension + 1) (dimension + 1)) :
    minor matrix 0 = tail matrix := by
  funext row column
  simp only [minor, tail, skipIndex, Fin.val_zero, Nat.not_lt_zero, ↓reduceIte]

public theorem UpperTriangular.tail {dimension : Nat}
    {matrix : carrier (dimension + 1) (dimension + 1)} (upper : UpperTriangular matrix) :
    UpperTriangular (tail matrix) :=
  fun row column below => upper row.succ column.succ (Nat.succ_lt_succ below)

/-- An upper triangular determinant is the leading diagonal entry times the
determinant of the tail. -/
public theorem det_succ_of_upperTriangular {dimension : Nat}
    {matrix : carrier (dimension + 1) (dimension + 1)} (upper : UpperTriangular matrix) :
    det matrix = mul (matrix 0 0) (det (tail matrix)) := by
  change sum (dimension + 1) (fun row =>
    mul (alternating row.val) (mul (matrix row 0) (det (minor matrix row)))) = _
  rw [sum_eq_single (dimension + 1) _ 0 (fun row other => by
    change mul (alternating row.val) (mul (matrix row 0) (det (minor matrix row))) = zero
    rw [upper row 0 (Fin.pos_iff_ne_zero.mpr other), zero_mul, mul_zero])]
  change mul (alternating (0 : Fin (dimension + 1)).val)
    (mul (matrix 0 0) (det (minor matrix 0))) = _
  rw [Fin.val_zero, minor_zero]
  change mul (if 0 % 2 = 0 then one else neg one) _ = _
  rw [ite_eq_left rfl, one_mul]

/-- An upper triangular determinant is nonzero exactly when every diagonal entry
is. -/
public theorem det_ne_zero_iff : {dimension : Nat} → {matrix : carrier dimension dimension} →
    UpperTriangular matrix → (det matrix ≠ zero ↔ ∀ index, matrix index index ≠ zero)
  | 0, _, _ => ⟨fun _ index => index.elim0, fun _ => one_ne_zero⟩
  | _ + 1, matrix, upper => by
      have rest := det_ne_zero_iff upper.tail
      rw [det_succ_of_upperTriangular upper]
      constructor
      · intro nonzero index
        refine Fin.cases ?_ (fun index => ?_) index
        · intro leading
          apply nonzero
          rw [leading, zero_mul]
        · exact rest.mp (fun restZero => nonzero (by rw [restZero, mul_zero])) index
      · intro diagonal vanishing
        exact rest.mpr (fun index => diagonal index.succ)
          ((mul_eq_zero_iff.mp vanishing).resolve_left (diagonal 0))

/-- An upper triangular matrix with a positive diagonal has a positive
determinant. -/
public theorem det_positive : {dimension : Nat} → {matrix : carrier dimension dimension} →
    UpperTriangular matrix → (∀ index, lt zero (matrix index index)) → lt zero (det matrix)
  | 0, _, _, _ => one_positive
  | _ + 1, _, upper, positive => by
      rw [det_succ_of_upperTriangular upper]
      exact mul_positive (positive 0)
        (det_positive upper.tail fun index => positive index.succ)

/-! ### Back substitution -/

/-- The first row of `matrix · x = target` read for `x 0`, given the tail of
`x`. -/
@[expose] public def solveStep {dimension : Nat}
    (matrix : carrier (dimension + 1) (dimension + 1))
    (target : FiniteVector.carrier (dimension + 1)) (rest : FiniteVector.carrier dimension) :
    FiniteVector.carrier (dimension + 1) :=
  fun index => Fin.cases
    (div (sub (target 0) (sum dimension fun column => mul (matrix 0 column.succ) (rest column)))
      (matrix 0 0))
    rest index

/-- Back substitution for an upper triangular system. -/
@[expose] public def solve : {dimension : Nat} → carrier dimension dimension →
    FiniteVector.carrier dimension → FiniteVector.carrier dimension
  | 0, _, target => target
  | _ + 1, matrix, target =>
      solveStep matrix target (solve (tail matrix) fun row => target row.succ)

/-- The first coordinate of an image splits into the leading column and the
rest. -/
public theorem apply_zero_row {dimension : Nat}
    (matrix : carrier (dimension + 1) (dimension + 1))
    (vector : FiniteVector.carrier (dimension + 1)) :
    apply matrix vector 0 =
      add (mul (matrix 0 0) (vector 0))
        (sum dimension fun column => mul (matrix 0 column.succ) (vector column.succ)) :=
  rfl

/-- Below the first row, an upper triangular matrix acts through its tail. -/
public theorem apply_succ_row {dimension : Nat}
    {matrix : carrier (dimension + 1) (dimension + 1)} (upper : UpperTriangular matrix)
    (vector : FiniteVector.carrier (dimension + 1)) (row : Fin dimension) :
    apply matrix vector row.succ = apply (tail matrix) (fun column => vector column.succ) row := by
  change add (mul (matrix row.succ 0) (vector 0)) _ = _
  rw [upper row.succ 0 (Fin.succ_pos row), zero_mul, zero_add]
  rfl

public theorem apply_solve : {dimension : Nat} → {matrix : carrier dimension dimension} →
    UpperTriangular matrix → (∀ index, matrix index index ≠ zero) →
    (target : FiniteVector.carrier dimension) → apply matrix (solve matrix target) = target
  | 0, _, _, _, _ => funext fun index => index.elim0
  | _ + 1, matrix, upper, diagonal, target => by
      funext row
      refine Fin.cases ?_ (fun row => ?_) row
      · rw [apply_zero_row]
        change add (mul (matrix 0 0) (div (sub (target 0)
            (sum _ fun column => mul (matrix 0 column.succ)
              (solve (tail matrix) (fun row => target row.succ) column))) (matrix 0 0)))
          (sum _ fun column => mul (matrix 0 column.succ)
            (solve (tail matrix) (fun row => target row.succ) column)) = target 0
        have leading := diagonal 0
        real_grind
      · rw [apply_succ_row upper]
        exact congrFun (apply_solve upper.tail (fun index => diagonal index.succ) _) row

public theorem solve_apply : {dimension : Nat} → {matrix : carrier dimension dimension} →
    UpperTriangular matrix → (∀ index, matrix index index ≠ zero) →
    (vector : FiniteVector.carrier dimension) → solve matrix (apply matrix vector) = vector
  | 0, _, _, _, _ => funext fun index => index.elim0
  | _ + 1, matrix, upper, diagonal, vector => by
      have rest : solve (tail matrix) (fun row => apply matrix vector row.succ) =
          fun column => vector column.succ := by
        rw [show (fun row => apply matrix vector row.succ) =
            apply (tail matrix) (fun column => vector column.succ) from
          funext (apply_succ_row upper vector)]
        exact solve_apply upper.tail (fun index => diagonal index.succ) _
      funext row
      change solveStep matrix (apply matrix vector)
        (solve (tail matrix) fun row => apply matrix vector row.succ) row = _
      rw [rest]
      refine Fin.cases ?_ (fun row => rfl) row
      change div (sub (add (mul (matrix 0 0) (vector 0))
          (sum _ fun column => mul (matrix 0 column.succ) (vector column.succ)))
        (sum _ fun column => mul (matrix 0 column.succ) (vector column.succ))) (matrix 0 0) =
        vector 0
      have leading := diagonal 0
      real_grind

/-- A 3 × 3 upper triangular determinant is the product of its diagonal. -/
example {matrix : carrier 3 3} (upper : UpperTriangular matrix) :
    det matrix = mul (matrix 0 0) (mul (matrix 1 1) (mul (matrix 2 2) one)) := by
  rw [det_succ_of_upperTriangular upper, det_succ_of_upperTriangular upper.tail,
    det_succ_of_upperTriangular upper.tail.tail]
  all_goals rfl

end

end Problib.Analysis.Real.Matrix
