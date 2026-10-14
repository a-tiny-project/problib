module

public import Problib.Analysis.Real.FiniteVector
public import Problib.Algebra.Sum
import Problib.Real.Grind

/-! Real matrices acting on finite vectors.

A matrix is a table of sealed reals, and it acts on `FiniteVector.carrier`, the
points that product volume measures. Every sum is `additiveLaws.finSum`, whose
successor split (the leading entry plus the rest) holds by `rfl`, so a proof by
induction on a dimension peels the same coordinate as `volumePi_succ`.

A product is read column by column: column `k` of `product A B` is `A` applied
to column `k` of `B`, by definition. Associativity of `product` is then the
composition law `apply (product A B) = apply A ∘ apply B` read at each column. The
Gram matrix `gram A` is `product (transpose A) A`: its entries are the inner
products of `A`'s columns.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.Matrix

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.FiniteVector (addVector subVector scaleVector zeroVector)

noncomputable section

/-! ### Finite sums of reals -/

/-- The sum of `dimension` reals, the leading entry first. -/
@[expose] public def sum (dimension : Nat) (values : Fin dimension → selection.Carrier) :
    selection.Carrier :=
  additiveLaws.finSum dimension values

public theorem sum_zero_dimension (values : Fin 0 → selection.Carrier) :
    sum 0 values = zero :=
  rfl

public theorem sum_succ (dimension : Nat) (values : Fin (dimension + 1) → selection.Carrier) :
    sum (dimension + 1) values =
      add (values 0) (sum dimension (fun index => values index.succ)) :=
  rfl

public theorem sum_congr (dimension : Nat) {left right : Fin dimension → selection.Carrier}
    (equal : ∀ index, left index = right index) : sum dimension left = sum dimension right :=
  congrArg (sum dimension) (funext equal)

public theorem sum_const_zero (dimension : Nat) :
    sum dimension (fun _ => zero) = zero :=
  additiveLaws.finSum_const_zero dimension

public theorem sum_add (dimension : Nat) (left right : Fin dimension → selection.Carrier) :
    sum dimension (fun index => add (left index) (right index)) =
      add (sum dimension left) (sum dimension right) :=
  additiveLaws.finSum_add dimension left right

public theorem sum_mul_left : (dimension : Nat) → (factor : selection.Carrier) →
    (values : Fin dimension → selection.Carrier) →
    sum dimension (fun index => mul factor (values index)) = mul factor (sum dimension values)
  | 0, factor, _ => (mul_zero factor).symm
  | dimension + 1, factor, values => by
      rw [sum_succ, sum_succ, sum_mul_left dimension factor]
      real_grind

public theorem sum_mul_right (dimension : Nat) (factor : selection.Carrier)
    (values : Fin dimension → selection.Carrier) :
    sum dimension (fun index => mul (values index) factor) = mul (sum dimension values) factor := by
  rw [mul_comm, ← sum_mul_left]
  exact sum_congr dimension fun index => mul_comm _ _

public theorem sum_neg : (dimension : Nat) → (values : Fin dimension → selection.Carrier) →
    sum dimension (fun index => neg (values index)) = neg (sum dimension values)
  | 0, _ => neg_zero.symm
  | dimension + 1, values => by
      rw [sum_succ, sum_succ, sum_neg dimension]
      real_grind

public theorem sum_sub (dimension : Nat) (left right : Fin dimension → selection.Carrier) :
    sum dimension (fun index => sub (left index) (right index)) =
      sub (sum dimension left) (sum dimension right) := by
  rw [sub_eq_add_neg, ← sum_neg, ← sum_add]
  exact sum_congr dimension fun index => sub_eq_add_neg _ _

/-- A double sum may be taken in either order. -/
public theorem sum_comm : (outer inner : Nat) →
    (values : Fin outer → Fin inner → selection.Carrier) →
    sum outer (fun first => sum inner (values first)) =
      sum inner (fun second => sum outer (fun first => values first second))
  | 0, inner, _ => (sum_const_zero inner).symm
  | outer + 1, inner, values => by
      rw [sum_succ, sum_comm outer inner, ← sum_add]
      rfl

/-- A sum whose terms vanish away from one index is that index's term. -/
public theorem sum_eq_single (dimension : Nat) (values : Fin dimension → selection.Carrier)
    (target : Fin dimension) (vanishing : ∀ index, index ≠ target → values index = zero) :
    sum dimension values = values target :=
  additiveLaws.finSum_eq_single dimension values target vanishing

/-! ### Matrices -/

/-- A real matrix with `rows` rows and `columns` columns. -/
@[expose, implicit_reducible] public def carrier (rows columns : Nat) : Type :=
  Fin rows → Fin columns → selection.Carrier

/-- The matrix acting on a vector. -/
@[expose] public def apply {rows columns : Nat} (matrix : carrier rows columns)
    (vector : FiniteVector.carrier columns) : FiniteVector.carrier rows :=
  fun row => sum columns (fun column => mul (matrix row column) (vector column))

/-- One column of a matrix. -/
@[expose] public def column {rows columns : Nat} (matrix : carrier rows columns)
    (index : Fin columns) : FiniteVector.carrier rows :=
  fun row => matrix row index

/-- The matrix with the given columns. -/
@[expose] public def ofColumns {rows columns : Nat}
    (columnVectors : Fin columns → FiniteVector.carrier rows) : carrier rows columns :=
  fun row index => columnVectors index row

@[expose] public def transpose {rows columns : Nat} (matrix : carrier rows columns) :
    carrier columns rows :=
  fun column row => matrix row column

/-- The product, column by column: column `k` of `product left right` is `left`
applied to column `k` of `right`. -/
@[expose] public def product {rows middle columns : Nat} (left : carrier rows middle)
    (right : carrier middle columns) : carrier rows columns :=
  fun row index => apply left (column right index) row

@[expose] public def identity (dimension : Nat) : carrier dimension dimension :=
  fun row column => if row = column then one else zero

/-- The Euclidean inner product. -/
@[expose] public def inner {dimension : Nat} (left right : FiniteVector.carrier dimension) :
    selection.Carrier :=
  sum dimension (fun index => mul (left index) (right index))

/-- The Gram matrix: the inner products of the columns. -/
@[expose] public def gram {rows columns : Nat} (matrix : carrier rows columns) :
    carrier columns columns :=
  product (transpose matrix) matrix

public theorem column_product {rows middle columns : Nat} (left : carrier rows middle)
    (right : carrier middle columns) (index : Fin columns) :
    column (product left right) index = apply left (column right index) :=
  rfl

public theorem gram_apply {rows columns : Nat} (matrix : carrier rows columns)
    (row column' : Fin columns) :
    gram matrix row column' = inner (column matrix row) (column matrix column') :=
  rfl

public theorem ext {rows columns : Nat} {left right : carrier rows columns}
    (equal : ∀ index, column left index = column right index) : left = right := by
  funext row index
  exact congrFun (equal index) row

/-! ### Linearity and composition -/

public theorem apply_add {rows columns : Nat} (matrix : carrier rows columns)
    (left right : FiniteVector.carrier columns) :
    apply matrix (addVector left right) = addVector (apply matrix left) (apply matrix right) := by
  funext row
  change sum columns _ = add (sum columns _) (sum columns _)
  rw [← sum_add]
  exact sum_congr columns fun index => mul_add _ _ _

public theorem apply_sub {rows columns : Nat} (matrix : carrier rows columns)
    (left right : FiniteVector.carrier columns) :
    apply matrix (subVector left right) = subVector (apply matrix left) (apply matrix right) := by
  funext row
  change sum columns _ = sub (sum columns _) (sum columns _)
  rw [← sum_sub]
  refine sum_congr columns fun index => ?_
  change mul _ (sub _ _) = sub _ _
  real_grind

public theorem apply_zero {rows columns : Nat} (matrix : carrier rows columns) :
    apply matrix (zeroVector columns) = zeroVector rows := by
  funext row
  change sum columns (fun index => mul (matrix row index) zero) = zero
  rw [sum_congr columns fun index => mul_zero (matrix row index)]
  exact sum_const_zero columns

/-- Applying a product applies its factors in turn. -/
public theorem apply_product {rows middle columns : Nat} (left : carrier rows middle)
    (right : carrier middle columns) (vector : FiniteVector.carrier columns) :
    apply (product left right) vector = apply left (apply right vector) := by
  funext row
  change sum columns (fun index => mul (sum middle fun middleIndex =>
      mul (left row middleIndex) (right middleIndex index)) (vector index)) =
    sum middle (fun middleIndex => mul (left row middleIndex)
      (sum columns fun index => mul (right middleIndex index) (vector index)))
  rw [sum_congr columns fun index => (sum_mul_right middle (vector index) _).symm,
    sum_comm columns middle]
  refine sum_congr middle fun middleIndex => ?_
  rw [← sum_mul_left]
  refine sum_congr columns fun index => ?_
  real_grind

public theorem product_assoc {rows first second columns : Nat} (left : carrier rows first)
    (middle : carrier first second) (right : carrier second columns) :
    product (product left middle) right = product left (product middle right) :=
  ext fun index => apply_product left middle (column right index)

public theorem apply_identity {dimension : Nat} (vector : FiniteVector.carrier dimension) :
    apply (identity dimension) vector = vector := by
  classical
  funext row
  change sum dimension (fun index => mul (if row = index then one else zero) (vector index)) = _
  rw [sum_eq_single dimension _ row (fun index other => by
    change mul (if row = index then one else zero) (vector index) = zero
    rw [ite_eq_right (Ne.symm other), zero_mul])]
  change mul (if row = row then one else zero) (vector row) = vector row
  rw [ite_eq_left rfl, one_mul]

public theorem identity_product {rows columns : Nat} (matrix : carrier rows columns) :
    product (identity rows) matrix = matrix :=
  ext fun index => apply_identity (column matrix index)

/-! ### Inner products -/

public theorem inner_comm {dimension : Nat} (left right : FiniteVector.carrier dimension) :
    inner left right = inner right left :=
  sum_congr dimension fun _ => mul_comm _ _

public theorem inner_scale_left {dimension : Nat} (factor : selection.Carrier)
    (left right : FiniteVector.carrier dimension) :
    inner (scaleVector factor left) right = mul factor (inner left right) := by
  change sum dimension (fun index => mul (mul factor (left index)) (right index)) =
    mul factor (sum dimension fun index => mul (left index) (right index))
  rw [← sum_mul_left]
  exact sum_congr dimension fun index => mul_assoc _ _ _

public theorem inner_scale_right {dimension : Nat} (factor : selection.Carrier)
    (left right : FiniteVector.carrier dimension) :
    inner left (scaleVector factor right) = mul factor (inner left right) := by
  rw [inner_comm, inner_scale_left, inner_comm]

public theorem inner_add_right {dimension : Nat} (left first second : FiniteVector.carrier dimension) :
    inner left (addVector first second) = add (inner left first) (inner left second) := by
  rw [inner, inner, inner, ← sum_add]
  exact sum_congr dimension fun index => mul_add _ _ _

public theorem inner_sub_right {dimension : Nat} (left first second : FiniteVector.carrier dimension) :
    inner left (subVector first second) = sub (inner left first) (inner left second) := by
  rw [inner, inner, inner, ← sum_sub]
  refine sum_congr dimension fun index => ?_
  change mul _ (sub _ _) = sub _ _
  real_grind

/-- A matrix moves across the inner product as its transpose. -/
public theorem inner_apply {rows columns : Nat} (matrix : carrier rows columns)
    (left : FiniteVector.carrier rows) (right : FiniteVector.carrier columns) :
    inner left (apply matrix right) = inner (apply (transpose matrix) left) right := by
  change sum rows (fun row => mul (left row)
      (sum columns fun index => mul (matrix row index) (right index))) =
    sum columns (fun index => mul
      (sum rows fun row => mul (matrix row index) (left row)) (right index))
  rw [sum_congr rows fun row => (sum_mul_left columns (left row) _).symm,
    sum_comm rows columns]
  refine sum_congr columns fun index => ?_
  rw [← sum_mul_right]
  refine sum_congr rows fun row => ?_
  real_grind

/-- The inner products of two images are read through the Gram matrix. -/
public theorem inner_apply_apply {rows columns : Nat} (matrix : carrier rows columns)
    (left right : FiniteVector.carrier columns) :
    inner (apply matrix left) (apply matrix right) = inner left (apply (gram matrix) right) := by
  rw [gram, apply_product, inner_apply (transpose matrix)]
  rfl

/-- The Gram matrix of a product. -/
public theorem gram_product {rows middle columns : Nat} (left : carrier rows middle)
    (right : carrier middle columns) :
    gram (product left right) = product (transpose right) (product (gram left) right) := by
  funext row index
  change inner (apply left (column right row)) (apply left (column right index)) =
    inner (column right row) (apply (gram left) (column right index))
  exact inner_apply_apply left _ _

end

end Problib.Analysis.Real.Matrix
