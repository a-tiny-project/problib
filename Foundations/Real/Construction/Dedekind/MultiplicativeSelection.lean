module

public import Foundations.Real.Construction.Dedekind.AdditiveSelection
public import Foundations.Real.Multiplicative
import all Foundations.Real.Construction.Dedekind.MulEmbedding
import all Foundations.Real.Construction.Dedekind.Multiplication

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Mul.lean,
MulAssoc.lean, and MulDistrib.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny exposes only the abstract ordered-ring capability and selected carrier
operations. The cut representation and construction witnesses remain sealed.
-/

namespace Foundations.Real.Construction.Dedekind

public noncomputable def multiplicativeSelection :
    OrderedCommutativeRingExtension additiveSelection where
  ring := ringLaws
  rational := {
    map_one := ringOfRatOne
    map_mul := fun left right => (ringOfRatMul left right).symm
  }

@[expose] public noncomputable def one : selection.Carrier :=
  multiplicativeSelection.ring.multiplicative.one

@[expose] public noncomputable def mul
    (left right : selection.Carrier) : selection.Carrier :=
  multiplicativeSelection.ring.multiplicative.mul left right

theorem oneEqRingOne :
    one = ringLaws.multiplicative.one :=
  rfl

theorem mulEqRingMul (left right : selection.Carrier) :
    mul left right = ringLaws.multiplicative.mul left right :=
  rfl

public theorem mulComm (left right : selection.Carrier) :
    mul left right = mul right left :=
  multiplicativeSelection.ring.multiplicative.mul_comm left right

public theorem mulAssoc (left middle right : selection.Carrier) :
    mul (mul left middle) right = mul left (mul middle right) :=
  multiplicativeSelection.ring.multiplicative.mul_assoc left middle right

public theorem mulOne (value : selection.Carrier) :
    mul value one = value :=
  multiplicativeSelection.ring.multiplicative.mul_one value

public theorem ofRatOne : selection.ofRat 1 = one :=
  multiplicativeSelection.rational.map_one

public theorem oneNonnegative : le zero one :=
  multiplicativeSelection.ring.one_nonnegative

public theorem mulAdd (left middle right : selection.Carrier) :
    mul left (add middle right) =
      add (mul left middle) (mul left right) :=
  multiplicativeSelection.ring.mul_add left middle right

public theorem mulNonnegative {left right : selection.Carrier}
    (leftNonnegative : le zero left) (rightNonnegative : le zero right) :
    le zero (mul left right) :=
  multiplicativeSelection.ring.product_nonnegative
    leftNonnegative rightNonnegative

public theorem mulLeMulNonnegativeRight
    {left right factor : selection.Carrier}
    (included : le left right) (factorNonnegative : le zero factor) :
    le (mul left factor) (mul right factor) :=
  multiplicativeSelection.ring.mulLeMulNonnegativeRight
    included factorNonnegative

public theorem mulLeMulNonnegativeLeft
    {left right factor : selection.Carrier}
    (included : le left right) (factorNonnegative : le zero factor) :
    le (mul factor left) (mul factor right) :=
  multiplicativeSelection.ring.mulLeMulNonnegativeLeft
    included factorNonnegative

public theorem ofRatMul (left right : Rat) :
    selection.ofRat (left * right) =
      mul (selection.ofRat left) (selection.ofRat right) :=
  multiplicativeSelection.rational.map_mul left right

end Foundations.Real.Construction.Dedekind
