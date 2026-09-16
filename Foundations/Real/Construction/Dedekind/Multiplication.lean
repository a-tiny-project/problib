module

import Foundations.Real.Multiplicative
import all Foundations.Algebra.Order.Multiplication
import all Foundations.Real.Construction.Dedekind.MultiplicationKernel

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Mul.lean,
MulNeg.lean, MulAssoc.lean, and MulDistrib.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny replaces the cut-specific signed proof chain with the generic signed
kernel extension. The concrete cut representation remains sealed.
-/

namespace Foundations.Real.Construction.Dedekind

noncomputable def ringLaws :
    Foundations.Algebra.OrderedCommutativeRingLaws
      additive.linearlyOrderedGroup :=
  multiplicationKernel.extend additive.linearlyOrderedGroup

theorem ringMul (left right : selection.Carrier) :
    ringLaws.multiplicative.mul left right =
      Foundations.Algebra.NonnegativeMultiplicationKernel.signedMul
        additive.linearlyOrderedGroup multiplicationKernel left right :=
  Foundations.Algebra.NonnegativeMultiplicationKernel.extendMul
    additive.linearlyOrderedGroup multiplicationKernel left right

end Foundations.Real.Construction.Dedekind
