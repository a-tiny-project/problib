module

public import Problib.Analysis.Real.Matrix.Algebra
public import Problib.Analysis.Sqrt
import Problib.Real.Grind

/-! The Euclidean norm, and matrices with orthonormal columns.

`norm v` is the square root of `inner v v`, which is a sum of squares and so
nonnegative, and zero only at the zero vector. A matrix has orthonormal
columns when its Gram matrix is the identity. Such a matrix keeps inner
products (`inner_apply_orthonormal`), so it carries `ℝ^d` isometrically into a
larger `ℝ^m`, and composing with it leaves a Gram matrix unchanged
(`gram_product_orthonormal`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.Matrix

open Problib.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.FiniteVector (zeroVector)

noncomputable section

public theorem sum_nonnegative : (dimension : Nat) → {values : Fin dimension → selection.Carrier} →
    (∀ index, le zero (values index)) → le zero (sum dimension values)
  | 0, _, _ => le_refl zero
  | dimension + 1, _, nonnegative =>
      add_nonnegative (nonnegative 0) (sum_nonnegative dimension fun index => nonnegative index.succ)

public theorem inner_self_nonnegative {dimension : Nat} (vector : FiniteVector.carrier dimension) :
    le zero (inner vector vector) :=
  sum_nonnegative dimension fun index => mul_self_nonnegative (vector index)

/-- A vector whose squares sum to zero is zero. -/
public theorem eq_zero_of_inner_self : {dimension : Nat} → {vector : FiniteVector.carrier dimension} →
    inner vector vector = zero → vector = zeroVector dimension
  | 0, _, _ => funext fun index => index.elim0
  | dimension + 1, vector, total => by
      have leading := mul_self_nonnegative (vector 0)
      have rest := inner_self_nonnegative (fun index : Fin dimension => vector index.succ)
      change add (mul (vector 0) (vector 0)) (inner (fun index => vector index.succ)
        (fun index => vector index.succ)) = zero at total
      have restZero : inner (fun index : Fin dimension => vector index.succ)
          (fun index => vector index.succ) = zero := by
        real_grind
      have leadingZero : vector 0 = zero := by
        have square : mul (vector 0) (vector 0) = zero := by real_grind
        exact (mul_eq_zero_iff.mp square).elim id id
      have tailZero := eq_zero_of_inner_self restZero
      funext index
      refine Fin.cases leadingZero (fun index => congrFun tailZero index) index

/-- The Euclidean norm. -/
@[expose] public def norm {dimension : Nat} (vector : FiniteVector.carrier dimension) :
    selection.Carrier :=
  (Problib.Analysis.sqrt (NNReal.ofReal (inner vector vector))).val

public theorem norm_mul_self {dimension : Nat} (vector : FiniteVector.carrier dimension) :
    mul (norm vector) (norm vector) = inner vector vector := by
  have square := congrArg NNReal.toReal
    (Problib.Analysis.sqrt_square (NNReal.ofReal (inner vector vector)))
  rw [NNReal.toReal_mul, NNReal.toReal_ofReal (inner_self_nonnegative vector)] at square
  exact square

public theorem norm_positive {dimension : Nat} {vector : FiniteVector.carrier dimension}
    (nonzero : vector ≠ zeroVector dimension) : lt zero (norm vector) := by
  have positive : lt zero (inner vector vector) := by
    have nonnegative := inner_self_nonnegative vector
    have distinct : inner vector vector ≠ zero := fun equal => nonzero (eq_zero_of_inner_self equal)
    real_grind
  have root := Problib.Analysis.sqrt_positive (NNReal.ofReal (inner vector vector)) (by
    change lt zero (NNReal.toReal (NNReal.ofReal (inner vector vector)))
    rwa [NNReal.toReal_ofReal (inner_self_nonnegative vector)])
  exact root

/-! ### Orthonormal columns -/

/-- The columns are orthonormal: the Gram matrix is the identity. -/
@[expose] public def Orthonormal {rows columns : Nat} (matrix : carrier rows columns) : Prop :=
  gram matrix = identity columns

/-- A matrix with orthonormal columns keeps inner products. -/
public theorem inner_apply_orthonormal {rows columns : Nat} {matrix : carrier rows columns}
    (orthonormal : Orthonormal matrix) (left right : FiniteVector.carrier columns) :
    inner (apply matrix left) (apply matrix right) = inner left right := by
  rw [inner_apply_apply, orthonormal, apply_identity]

/-- Composing with orthonormal columns leaves the Gram matrix unchanged. -/
public theorem gram_product_orthonormal {rows middle columns : Nat} {left : carrier rows middle}
    (orthonormal : Orthonormal left) (right : carrier middle columns) :
    gram (product left right) = gram right := by
  rw [gram_product, orthonormal, identity_product]
  rfl

end

end Problib.Analysis.Real.Matrix
