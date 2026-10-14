module

public import Problib.Analysis.Real.Matrix.Determinant
public import Problib.Analysis.Real.Matrix.Gram
import Problib.Real.Grind

/-! QR factorization by Gram–Schmidt.

A matrix `A` with independent columns factors as `A = Q R`, where `Q` has
orthonormal columns and `R` is upper triangular with a positive diagonal. This
is the factorization through which a full-column-rank linear map `ℝ^d → ℝ^m`
becomes an isometric embedding `Q` after a square change of coordinates `R`.

`orthonormalize` is the modified Gram–Schmidt process, read from the first
column. It normalizes column 0 to `q₀`, removes the `q₀` component from every
later column (`deflate`), and orthonormalizes those columns. The recursion
peels the first column, like `solve` and `det`, so each step reduces by `rfl`.
`R` is `Qᵀ A`, the inner products `⟨q_i, a_j⟩`.

Every fact is proved in one induction (`orthonormalize_facts`). Besides the
factorization itself, it carries a statement about column spaces: a vector
orthogonal to every column of `A` is orthogonal to every column of `Q`. The
step uses this to show `q₀` is orthogonal to the columns built after it.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.Matrix

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.FiniteVector (addVector subVector scaleVector zeroVector)

noncomputable section

/-- Only the zero combination of the columns is zero. -/
@[expose] public def Independent {rows columns : Nat} (matrix : carrier rows columns) : Prop :=
  ∀ coefficients, apply matrix coefficients = zeroVector rows → coefficients = zeroVector columns

/-- The matrix with `first` prepended as column 0. -/
@[expose] public def consColumn {rows columns : Nat} (first : FiniteVector.carrier rows)
    (rest : carrier rows columns) : carrier rows (columns + 1) :=
  fun row index => Fin.cases (first row) (rest row) index

/-- The columns after column 0. -/
@[expose] public def restColumns {rows columns : Nat} (matrix : carrier rows (columns + 1)) :
    carrier rows columns :=
  fun row index => matrix row index.succ

/-- The unit vector along `vector`. -/
@[expose] public def normalize {rows : Nat} (vector : FiniteVector.carrier rows) :
    FiniteVector.carrier rows :=
  scaleVector (inverse (norm vector)) vector

/-- Each column without its component along the unit vector `unit`. -/
@[expose] public def deflate {rows columns : Nat} (unit : FiniteVector.carrier rows)
    (matrix : carrier rows columns) : carrier rows columns :=
  fun row index => sub (matrix row index) (mul (inner unit (column matrix index)) (unit row))

/-- Modified Gram–Schmidt. -/
@[expose] public def orthonormalize {rows : Nat} :
    {columns : Nat} → carrier rows columns → carrier rows columns
  | 0, matrix => matrix
  | _ + 1, matrix =>
      consColumn (normalize (column matrix 0))
        (orthonormalize (deflate (normalize (column matrix 0)) (restColumns matrix)))

/-! ### Columns -/

public theorem apply_consColumn {rows columns : Nat} (first : FiniteVector.carrier rows)
    (rest : carrier rows columns) (coefficients : FiniteVector.carrier (columns + 1)) :
    apply (consColumn first rest) coefficients =
      addVector (scaleVector (coefficients 0) first)
        (apply rest fun index => coefficients index.succ) := by
  funext row
  change add (mul (first row) (coefficients 0)) _ = add (mul (coefficients 0) (first row)) _
  rw [mul_comm (first row) (coefficients 0)]
  rfl

/-- `apply matrix` on a vector split as its first coordinate and the rest. -/
public theorem apply_cases {rows columns : Nat} (matrix : carrier rows (columns + 1))
    (head : selection.Carrier) (rest : FiniteVector.carrier columns) :
    apply matrix (fun index => Fin.cases head rest index) =
      addVector (scaleVector head (column matrix 0)) (apply (restColumns matrix) rest) := by
  funext row
  change add (mul (matrix row 0) head) _ = add (mul head (matrix row 0)) _
  rw [mul_comm (matrix row 0) head]
  rfl

public theorem column_deflate {rows columns : Nat} (unit : FiniteVector.carrier rows)
    (matrix : carrier rows columns) (index : Fin columns) :
    column (deflate unit matrix) index =
      subVector (column matrix index) (scaleVector (inner unit (column matrix index)) unit) :=
  rfl

public theorem apply_deflate {rows columns : Nat} (unit : FiniteVector.carrier rows)
    (matrix : carrier rows columns) (coefficients : FiniteVector.carrier columns) :
    apply (deflate unit matrix) coefficients =
      subVector (apply matrix coefficients)
        (scaleVector (inner unit (apply matrix coefficients)) unit) := by
  have expand : inner unit (apply matrix coefficients) =
      sum columns (fun index => mul (inner unit (column matrix index)) (coefficients index)) := by
    rw [inner_apply]
    exact sum_congr columns fun index =>
      congrArg (fun value => mul value (coefficients index)) (inner_comm _ _)
  funext row
  rw [expand]
  change sum columns (fun index => mul (sub (matrix row index)
      (mul (inner unit (column matrix index)) (unit row))) (coefficients index)) =
    sub (sum columns fun index => mul (matrix row index) (coefficients index))
      (mul (sum columns fun index =>
        mul (inner unit (column matrix index)) (coefficients index)) (unit row))
  rw [← sum_mul_right, ← sum_sub]
  refine sum_congr columns fun index => ?_
  real_grind

/-- The transpose applied to `w` lists the inner products of the columns with
`w`. -/
public theorem apply_transpose {rows columns : Nat} (matrix : carrier rows columns)
    (vector : FiniteVector.carrier rows) (index : Fin columns) :
    apply (transpose matrix) vector index = inner (column matrix index) vector :=
  rfl

/-! ### The unit vector of a nonzero column -/

private theorem norm_ne_zero {rows : Nat} {vector : FiniteVector.carrier rows}
    (nonzero : vector ≠ zeroVector rows) : norm vector ≠ zero := by
  have positive := norm_positive nonzero
  real_grind

public theorem inner_normalize_self {rows : Nat} {vector : FiniteVector.carrier rows}
    (nonzero : vector ≠ zeroVector rows) :
    inner (normalize vector) (normalize vector) = one := by
  have square := norm_mul_self vector
  have distinct := norm_ne_zero nonzero
  rw [normalize, inner_scale_left, inner_scale_right, ← square]
  real_grind

public theorem inner_normalize {rows : Nat} (vector other : FiniteVector.carrier rows) :
    inner (normalize vector) other = mul (inverse (norm vector)) (inner vector other) :=
  inner_scale_left _ _ _

/-- A nonzero vector is its norm times its unit vector. -/
public theorem scale_normalize {rows : Nat} {vector : FiniteVector.carrier rows}
    (nonzero : vector ≠ zeroVector rows) :
    scaleVector (norm vector) (normalize vector) = vector := by
  have distinct := norm_ne_zero nonzero
  funext row
  change mul (norm vector) (mul (inverse (norm vector)) (vector row)) = vector row
  real_grind

/-! ### The induction -/

/-- What Gram–Schmidt delivers for `matrix`, with `basis` its orthonormalized
columns. -/
public structure GramSchmidt {rows columns : Nat} (matrix basis : carrier rows columns) :
    Prop where
  orthonormal : Orthonormal basis
  upper : UpperTriangular (product (transpose basis) matrix)
  positive : ∀ index, lt zero (product (transpose basis) matrix index index)
  factor : product basis (product (transpose basis) matrix) = matrix
  span : ∀ vector, apply (transpose matrix) vector = zeroVector columns →
    apply (transpose basis) vector = zeroVector columns

private theorem identity_succ {columns : Nat} (row column : Fin columns) :
    identity (columns + 1) row.succ column.succ = identity columns row column := by
  classical
  by_cases same : row = column
  · rw [identity, identity, ite_eq_left (congrArg Fin.succ same), ite_eq_left same]
  · rw [identity, identity, ite_eq_right (fun equal => same (Fin.succ_inj.mp equal)), ite_eq_right same]

private theorem identity_zero_succ {columns : Nat} (column : Fin columns) :
    identity (columns + 1) 0 column.succ = zero :=
  ite_eq_right (Fin.succ_ne_zero column).symm

private theorem identity_succ_zero {columns : Nat} (row : Fin columns) :
    identity (columns + 1) row.succ 0 = zero :=
  ite_eq_right (Fin.succ_ne_zero row)

private theorem gramSchmidt_zero {rows : Nat} (matrix : carrier rows 0) :
    GramSchmidt matrix (orthonormalize matrix) where
  orthonormal := funext fun index => index.elim0
  upper := fun index => index.elim0
  positive := fun index => index.elim0
  factor := funext fun _ => funext fun index => index.elim0
  span := fun _ _ => funext fun index => index.elim0

private theorem gramSchmidt_succ {rows columns : Nat} (matrix : carrier rows (columns + 1))
    (independent : Independent matrix)
    (induction : ∀ smaller : carrier rows columns, Independent smaller →
      GramSchmidt smaller (orthonormalize smaller)) :
    GramSchmidt matrix (orthonormalize matrix) := by
  let leading := column matrix 0
  let unit := normalize leading
  let rest := deflate unit (restColumns matrix)
  let basis := orthonormalize rest
  have leadingNonzero : leading ≠ zeroVector rows := by
    intro vanishing
    have combination := independent (fun index => Fin.cases one (zeroVector columns) index) (by
      rw [apply_cases, apply_zero]
      funext row
      have entry : leading row = zero := congrFun vanishing row
      change add (mul one (leading row)) zero = zero
      rw [entry]
      real_grind)
    exact one_ne_zero (congrFun combination 0)
  have unitSelf : inner unit unit = one := inner_normalize_self leadingNonzero
  have unitLeading : inner unit leading = norm leading := by
    rw [inner_normalize, ← norm_mul_self leading]
    have distinct := norm_ne_zero leadingNonzero
    real_grind
  have leadingScale : scaleVector (norm leading) unit = leading := scale_normalize leadingNonzero
  have restIndependent : Independent rest := by
    intro coefficients vanishing
    rw [apply_deflate] at vanishing
    let amount := inner unit (apply (restColumns matrix) coefficients)
    have combination := independent
      (fun index => Fin.cases (neg (mul amount (inverse (norm leading)))) coefficients index) (by
        rw [apply_cases]
        funext row
        have restRow : sub (apply (restColumns matrix) coefficients row)
            (mul amount (mul (inverse (norm leading)) (leading row))) = zero :=
          congrFun vanishing row
        change add (mul (neg (mul amount (inverse (norm leading)))) (leading row))
          (apply (restColumns matrix) coefficients row) = zero
        real_grind)
    funext index
    exact congrFun combination index.succ
  have facts := induction rest restIndependent
  have orthonormalBasis : gram basis = identity columns := facts.orthonormal
  -- Every column built after `unit` is orthogonal to it.
  have restUnit : apply (transpose rest) unit = zeroVector columns := by
    funext index
    change inner (column rest index) unit = zero
    rw [inner_comm, column_deflate, inner_sub_right, inner_scale_right, unitSelf]
    real_grind
  have basisUnit (index : Fin columns) : inner (column basis index) unit = zero :=
    congrFun (facts.span unit restUnit) index
  have basisLeading (index : Fin columns) : inner (column basis index) leading = zero := by
    rw [← leadingScale, inner_scale_right, basisUnit]
    exact mul_zero _
  -- Below row 0, the coefficients of `matrix` are those of `rest`.
  have coefficient (row : Fin columns) (index : Fin columns) :
      inner (column basis row) (column matrix index.succ) =
        product (transpose basis) rest row index := by
    change _ = inner (column basis row) (column rest index)
    rw [column_deflate, inner_sub_right, inner_scale_right, basisUnit, mul_zero]
    change inner (column basis row) (column matrix index.succ) =
      sub (inner (column basis row) (column matrix index.succ)) zero
    real_grind
  change GramSchmidt matrix (consColumn unit basis)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change gram (consColumn unit basis) = identity (columns + 1)
    funext row index
    rw [gram_apply]
    refine Fin.cases ?_ (fun row => ?_) row
    · refine Fin.cases ?_ (fun index => ?_) index
      · change inner unit unit = identity (columns + 1) 0 0
        rw [unitSelf]
        exact (ite_eq_left rfl).symm
      · exact ((inner_comm _ _).trans (basisUnit index)).trans (identity_zero_succ index).symm
    · refine Fin.cases ?_ (fun index => ?_) index
      · exact (basisUnit row).trans (identity_succ_zero row).symm
      · exact (congrFun (congrFun orthonormalBasis row) index).trans
          (identity_succ row index).symm
  · intro row index below
    refine Fin.cases (fun below => absurd below (by simp))
      (fun row below => ?_) row below
    refine Fin.cases (fun _ => basisLeading row) (fun index below => ?_) index below
    exact (coefficient row index).trans (facts.upper row index (Nat.lt_of_succ_lt_succ below))
  · intro index
    refine Fin.cases ?_ (fun index => ?_) index
    · change lt zero (inner unit leading)
      rw [unitLeading]
      exact norm_positive leadingNonzero
    · change lt zero (inner (column basis index) (column matrix index.succ))
      rw [coefficient]
      exact facts.positive index
  · refine ext fun index => ?_
    rw [column_product, apply_consColumn]
    refine Fin.cases ?_ (fun index => ?_) index
    · have below : (fun row : Fin columns => inner (column basis row) leading) = zeroVector columns :=
        funext basisLeading
      change addVector (scaleVector (inner unit leading) unit)
        (apply basis fun row => inner (column basis row) leading) = leading
      rw [below, apply_zero, unitLeading, leadingScale]
      funext row
      change add (leading row) zero = leading row
      real_grind
    · have below : (fun row : Fin columns => inner (column basis row) (column matrix index.succ)) =
          column (product (transpose basis) rest) index :=
        funext fun row => coefficient row index
      change addVector (scaleVector (inner unit (column matrix index.succ)) unit)
        (apply basis fun row => inner (column basis row) (column matrix index.succ)) = _
      rw [below, ← column_product, facts.factor, column_deflate]
      funext row
      change add (mul (inner unit (column matrix index.succ)) (unit row))
        (sub (matrix row index.succ) (mul (inner unit (column matrix index.succ)) (unit row))) =
        matrix row index.succ
      real_grind
  · intro vector orthogonal
    have entry (index : Fin (columns + 1)) : inner (column matrix index) vector = zero :=
      congrFun orthogonal index
    have unitVector : inner unit vector = zero := by
      rw [inner_normalize, entry 0, mul_zero]
    have restVector : apply (transpose rest) vector = zeroVector columns := by
      funext index
      change inner (column rest index) vector = zero
      rw [inner_comm, column_deflate, inner_sub_right, inner_scale_right, inner_comm vector unit,
        unitVector, mul_zero]
      change sub (inner vector (column matrix index.succ)) zero = zero
      rw [inner_comm, entry index.succ]
      real_grind
    funext index
    refine Fin.cases unitVector (fun index => congrFun (facts.span vector restVector) index) index

/-- Gram–Schmidt on independent columns: the orthonormalized columns `Q` and
`R = Qᵀ A` factor `A = Q R`, with `R` upper triangular and its diagonal
positive. -/
public theorem orthonormalize_facts {rows : Nat} :
    {columns : Nat} → (matrix : carrier rows columns) → Independent matrix →
      GramSchmidt matrix (orthonormalize matrix)
  | 0, matrix, _ => gramSchmidt_zero matrix
  | _ + 1, matrix, independent =>
      gramSchmidt_succ matrix independent fun smaller => orthonormalize_facts smaller

/-- The Gram matrix of `A = Q R` is `Rᵀ R`. -/
public theorem gram_eq_of_factor {rows columns : Nat} {matrix : carrier rows columns}
    (independent : Independent matrix) :
    gram matrix = gram (product (transpose (orthonormalize matrix)) matrix) := by
  have facts := orthonormalize_facts matrix independent
  conv => lhs; rw [← facts.factor]
  exact gram_product_orthonormal facts.orthonormal _

end

end Problib.Analysis.Real.Matrix
