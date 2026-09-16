import Foundations.Probability.NNRat
import Foundations.Real.Extended.Conversion

set_option autoImplicit false

namespace Foundations.Probability.NNRat

open Foundations.Real

/-- Faithful embedding of non-negative rationals `NNRat` into `ENNReal`. -/
noncomputable def toENNReal (value : NNRat) : ENNReal :=
  ENNReal.ofRat value.val value.nonnegative

/-- The embedding preserves zero. -/
@[simp] theorem toENNReal_zero : toENNReal 0 = ENNReal.zero :=
  ENNReal.ofRatZero

/-- The embedding preserves one. -/
@[simp] theorem toENNReal_one : toENNReal 1 = ENNReal.one :=
  ENNReal.ofRatOne

/-- The embedding preserves addition. -/
theorem toENNReal_add (left right : NNRat) :
    toENNReal (left + right) = ENNReal.add left.toENNReal right.toENNReal :=
  ENNReal.ofRatAdd left.val right.val left.nonnegative right.nonnegative

/-- The embedding preserves multiplication. -/
theorem toENNReal_mul (left right : NNRat) :
    toENNReal (left * right) = ENNReal.mul left.toENNReal right.toENNReal :=
  ENNReal.ofRatMul left.val right.val left.nonnegative right.nonnegative

/-- The embedding of `NNRat` into `ENNReal` is injective. -/
theorem toENNReal_injective {left right : NNRat}
    (equal : left.toENNReal = right.toENNReal) : left = right := by
  apply NNRat.ext
  exact Construction.Dedekind.ofRatInjective (congrArg ENNReal.toReal equal)

/-- An embedded rational is zero in `ENNReal` iff the original `NNRat` is zero. -/
@[simp] theorem toENNReal_eq_zero_iff (value : NNRat) :
    value.toENNReal = ENNReal.zero ↔ value = 0 :=
  ⟨fun equal => toENNReal_injective (equal.trans toENNReal_zero.symm),
    fun equal => by rw [equal, toENNReal_zero]⟩

/-- Every embedded non-negative rational has finite value in `ENNReal`. -/
theorem toENNReal_finite (value : NNRat) : ENNReal.Finite value.toENNReal :=
  True.intro

end Foundations.Probability.NNRat
