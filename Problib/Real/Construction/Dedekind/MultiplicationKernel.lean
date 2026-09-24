module

import Problib.Algebra.Order.Nonnegative
import all Problib.Real.Construction.Dedekind.MulNonnegativeDistributive
import all Problib.Real.Construction.Dedekind.Selection

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/MulNonneg.lean and
MulNonnegDistrib.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny packages the retained cut proofs behind the generic nonnegative
multiplication kernel. The cut carrier and proof arguments remain sealed.
-/

namespace Problib.Real.Construction.Dedekind

private abbrev Nonnegative :=
  Problib.Algebra.NonnegativePart additive.orderedGroup

private theorem cut_nonnegative (value : Nonnegative) :
    (0 : Cut) ≤ value.val := by
  exact value.property

private def nonnegativeOne : Nonnegative :=
  ⟨(1 : Cut), by
    intro rational negative
    exact Rational.lt_of_lt_of_le negative (by decide)⟩

private def nonnegativeMul (left right : Nonnegative) : Nonnegative :=
  ⟨Cut.mulNonnegative left.val right.val
      (cut_nonnegative left) (cut_nonnegative right),
    Cut.mulNonnegative_nonnegative left.val right.val
      (cut_nonnegative left) (cut_nonnegative right)⟩

private theorem nonnegativeMul_comm (left right : Nonnegative) :
    nonnegativeMul left right = nonnegativeMul right left := by
  apply Problib.Algebra.NonnegativePart.ext
  exact Cut.mulNonnegative_comm left.val right.val
    (cut_nonnegative left) (cut_nonnegative right)

private theorem nonnegativeMul_assoc
    (left middle right : Nonnegative) :
    nonnegativeMul (nonnegativeMul left middle) right =
      nonnegativeMul left (nonnegativeMul middle right) := by
  apply Problib.Algebra.NonnegativePart.ext
  exact Cut.mulNonnegative_assoc left.val middle.val right.val
    (cut_nonnegative left) (cut_nonnegative middle) (cut_nonnegative right)

private theorem nonnegativeMul_one (value : Nonnegative) :
    nonnegativeMul value nonnegativeOne = value := by
  apply Problib.Algebra.NonnegativePart.ext
  exact Cut.mulNonnegative_one_right value.val (cut_nonnegative value)

private theorem nonnegativeMul_add
    (factor left right : Nonnegative) :
    nonnegativeMul factor
        (Problib.Algebra.NonnegativePart.add left right) =
      Problib.Algebra.NonnegativePart.add
        (nonnegativeMul factor left) (nonnegativeMul factor right) := by
  apply Problib.Algebra.NonnegativePart.ext
  exact Cut.mulNonnegative_add_left factor.val left.val right.val
    (cut_nonnegative factor) (cut_nonnegative left) (cut_nonnegative right)

def multiplicationKernel :
    Problib.Algebra.NonnegativeMultiplicationKernel
      additive.orderedGroup where
  one := nonnegativeOne
  mul := nonnegativeMul
  mul_comm := nonnegativeMul_comm
  mul_assoc := nonnegativeMul_assoc
  mul_one := nonnegativeMul_one
  mul_add := nonnegativeMul_add

end Problib.Real.Construction.Dedekind
