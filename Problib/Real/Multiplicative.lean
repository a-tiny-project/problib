module

public import Problib.Algebra.Order.Multiplication
public import Problib.Real.Additive

namespace Problib.Real

public structure RationalMultiplicativeHomomorphism (α : Type)
    (one : α) (mul : α → α → α) (ofRat : Rat → α) where
  map_one : ofRat 1 = one
  map_mul : ∀ left right,
    ofRat (left * right) = mul (ofRat left) (ofRat right)

public structure OrderedCommutativeRingExtension
    (base : AdditiveSelection) where
  ring : Problib.Algebra.OrderedCommutativeRingLaws
    base.linearlyOrderedGroup
  rational : RationalMultiplicativeHomomorphism base.ordered.Carrier
    ring.multiplicative.one ring.multiplicative.mul base.ordered.ofRat

end Problib.Real
