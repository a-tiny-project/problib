module

import Foundations.Algebra.Order.Nonnegative
import all Foundations.Real.Construction.Dedekind.MulNonnegativeDistributive
import all Foundations.Real.Construction.Dedekind.Selection

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/MulNonneg.lean and
MulNonnegDistrib.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny packages the retained cut proofs behind the generic nonnegative
multiplication kernel. The cut carrier and proof arguments remain sealed.
-/

namespace Foundations.Real.Construction.Dedekind

private abbrev Nonnegative :=
  Foundations.Algebra.NonnegativePart additive.orderedGroup

private theorem cutNonnegative (value : Nonnegative) :
    (0 : Cut) ≤ value.val := by
  exact value.property

private def nonnegativeOne : Nonnegative :=
  ⟨(1 : Cut), by
    intro rational negative
    exact Rational.ltOfLtOfLe negative (by decide)⟩

private def nonnegativeMul (left right : Nonnegative) : Nonnegative :=
  ⟨Cut.mulNonnegative left.val right.val
      (cutNonnegative left) (cutNonnegative right),
    Cut.mulNonnegativeNonnegative left.val right.val
      (cutNonnegative left) (cutNonnegative right)⟩

private theorem nonnegativeMulComm (left right : Nonnegative) :
    nonnegativeMul left right = nonnegativeMul right left := by
  apply Foundations.Algebra.NonnegativePart.ext
  exact Cut.mulNonnegativeComm left.val right.val
    (cutNonnegative left) (cutNonnegative right)

private theorem nonnegativeMulAssoc
    (left middle right : Nonnegative) :
    nonnegativeMul (nonnegativeMul left middle) right =
      nonnegativeMul left (nonnegativeMul middle right) := by
  apply Foundations.Algebra.NonnegativePart.ext
  exact Cut.mulNonnegativeAssoc left.val middle.val right.val
    (cutNonnegative left) (cutNonnegative middle) (cutNonnegative right)

private theorem nonnegativeMulOne (value : Nonnegative) :
    nonnegativeMul value nonnegativeOne = value := by
  apply Foundations.Algebra.NonnegativePart.ext
  exact Cut.mulNonnegativeOneRight value.val (cutNonnegative value)

private theorem nonnegativeMulAdd
    (factor left right : Nonnegative) :
    nonnegativeMul factor
        (Foundations.Algebra.NonnegativePart.add left right) =
      Foundations.Algebra.NonnegativePart.add
        (nonnegativeMul factor left) (nonnegativeMul factor right) := by
  apply Foundations.Algebra.NonnegativePart.ext
  exact Cut.mulNonnegativeAddLeft factor.val left.val right.val
    (cutNonnegative factor) (cutNonnegative left) (cutNonnegative right)

def multiplicationKernel :
    Foundations.Algebra.NonnegativeMultiplicationKernel
      additive.orderedGroup where
  one := nonnegativeOne
  mul := nonnegativeMul
  mul_comm := nonnegativeMulComm
  mul_assoc := nonnegativeMulAssoc
  mul_one := nonnegativeMulOne
  mul_add := nonnegativeMulAdd

end Foundations.Real.Construction.Dedekind
