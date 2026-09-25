module

import Problib.Real.Multiplicative
import all Problib.Algebra.Order.Multiplication
import all Problib.Real.Construction.Dedekind.MultiplicationKernel

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Mul.lean,
MulNeg.lean, MulAssoc.lean, and MulDistrib.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny replaces the cut-specific signed proof chain with the generic signed
kernel extension. The concrete cut representation remains sealed.
-/

namespace Problib.Real.Construction.Dedekind

noncomputable def ringLaws :
    Problib.Algebra.OrderedCommutativeRingLaws
      additive.linearlyOrderedGroup :=
  multiplicationKernel.extend additive.linearlyOrderedGroup

theorem ring_mul (left right : selection.Carrier) :
    ringLaws.multiplicative.mul left right =
      Problib.Algebra.NonnegativeMultiplicationKernel.signedMul
        additive.linearlyOrderedGroup multiplicationKernel left right :=
  Problib.Algebra.NonnegativeMultiplicationKernel.extend_mul
    additive.linearlyOrderedGroup multiplicationKernel left right

end Problib.Real.Construction.Dedekind
