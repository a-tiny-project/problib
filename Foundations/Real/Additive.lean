module

public import Foundations.Real.Interface

namespace Foundations.Real

namespace RationalAdditiveHomomorphism

public theorem mapZero {α : Type}
    (laws : Foundations.Algebra.AdditiveCommutativeGroupLaws α)
    (ofRat : Rat → α)
    (homomorphism : RationalAdditiveHomomorphism α laws.add ofRat) :
    ofRat 0 = laws.zero := by
  apply Foundations.Algebra.AdditiveCommutativeGroupLaws.addLeftCancel laws
    (left := ofRat 0)
  calc
    laws.add (ofRat 0) (ofRat 0) = ofRat (0 + 0) :=
      (homomorphism.map_add 0 0).symm
    _ = ofRat 0 := by rw [Rat.zero_add]
    _ = laws.add (ofRat 0) laws.zero := (laws.add_zero _).symm

public theorem mapNeg {α : Type}
    (laws : Foundations.Algebra.AdditiveCommutativeGroupLaws α)
    (ofRat : Rat → α)
    (homomorphism : RationalAdditiveHomomorphism α laws.add ofRat)
    (value : Rat) :
    ofRat (-value) = laws.neg (ofRat value) := by
  apply Foundations.Algebra.AdditiveCommutativeGroupLaws.addLeftCancel laws
    (left := ofRat value)
  calc
    laws.add (ofRat value) (ofRat (-value)) = ofRat (value + -value) :=
      (homomorphism.map_add value (-value)).symm
    _ = ofRat 0 := by rw [Rat.add_neg_cancel]
    _ = laws.zero := mapZero laws ofRat homomorphism
    _ = laws.add (ofRat value) (laws.neg (ofRat value)) :=
      (laws.add_neg _).symm

public theorem mapSub {α : Type}
    (laws : Foundations.Algebra.AdditiveCommutativeGroupLaws α)
    (ofRat : Rat → α)
    (homomorphism : RationalAdditiveHomomorphism α laws.add ofRat)
    (left right : Rat) :
    ofRat (left - right) = laws.sub (ofRat left) (ofRat right) := by
  rw [Rat.sub_eq_add_neg, homomorphism.map_add,
    mapNeg laws ofRat homomorphism]
  rfl

end RationalAdditiveHomomorphism

end Foundations.Real
