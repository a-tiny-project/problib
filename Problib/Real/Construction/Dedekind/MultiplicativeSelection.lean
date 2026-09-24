module

public import Problib.Real.Construction.Dedekind.AdditiveSelection
public import Problib.Real.Multiplicative
import all Problib.Real.Construction.Dedekind.MulEmbedding
import all Problib.Real.Construction.Dedekind.Multiplication

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Mul.lean,
MulAssoc.lean, and MulDistrib.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny exposes only the abstract ordered-ring capability and selected carrier
operations. The cut representation and construction witnesses remain sealed.
-/

namespace Problib.Real.Construction.Dedekind

public noncomputable def multiplicativeSelection :
    OrderedCommutativeRingExtension additiveSelection where
  ring := ringLaws
  rational := {
    map_one := ring_ofRat_one
    map_mul := fun left right => (ring_ofRat_mul left right).symm
  }

@[expose] public noncomputable def one : selection.Carrier :=
  multiplicativeSelection.ring.multiplicative.one

@[expose] public noncomputable def mul
    (left right : selection.Carrier) : selection.Carrier :=
  multiplicativeSelection.ring.multiplicative.mul left right

theorem one_eq_ring_one :
    one = ringLaws.multiplicative.one :=
  rfl

theorem mul_eq_ring_mul (left right : selection.Carrier) :
    mul left right = ringLaws.multiplicative.mul left right :=
  rfl

public theorem mul_comm (left right : selection.Carrier) :
    mul left right = mul right left :=
  multiplicativeSelection.ring.multiplicative.mul_comm left right

public theorem mul_assoc (left middle right : selection.Carrier) :
    mul (mul left middle) right = mul left (mul middle right) :=
  multiplicativeSelection.ring.multiplicative.mul_assoc left middle right

public theorem mul_one (value : selection.Carrier) :
    mul value one = value :=
  multiplicativeSelection.ring.multiplicative.mul_one value

public theorem ofRat_one : selection.ofRat 1 = one :=
  multiplicativeSelection.rational.map_one

public theorem one_nonnegative : le zero one :=
  multiplicativeSelection.ring.one_nonnegative

public theorem mul_add (left middle right : selection.Carrier) :
    mul left (add middle right) =
      add (mul left middle) (mul left right) :=
  multiplicativeSelection.ring.mul_add left middle right

public theorem mul_nonnegative {left right : selection.Carrier}
    (leftNonnegative : le zero left) (rightNonnegative : le zero right) :
    le zero (mul left right) :=
  multiplicativeSelection.ring.product_nonnegative
    leftNonnegative rightNonnegative

public theorem mul_le_mul_nonnegative_right
    {left right factor : selection.Carrier}
    (included : le left right) (factorNonnegative : le zero factor) :
    le (mul left factor) (mul right factor) :=
  multiplicativeSelection.ring.mul_le_mul_nonnegative_right
    included factorNonnegative

public theorem mul_le_mul_nonnegative_left
    {left right factor : selection.Carrier}
    (included : le left right) (factorNonnegative : le zero factor) :
    le (mul factor left) (mul factor right) :=
  multiplicativeSelection.ring.mul_le_mul_nonnegative_left
    included factorNonnegative

public theorem ofRat_mul (left right : Rat) :
    selection.ofRat (left * right) =
      mul (selection.ofRat left) (selection.ofRat right) :=
  multiplicativeSelection.rational.map_mul left right

end Problib.Real.Construction.Dedekind
