import Foundations.Algebra
import Foundations.Algebra.Order.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Algebra.AdditiveCommutativeMonoidLaws.zeroAdd,
  Foundations.Algebra.AdditiveCommutativeMonoidLaws.addLeftComm,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.subEqAddNeg,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.zeroAdd,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.negAdd,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.addNegCancelRight,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.negAddCancelLeft,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.addLeftCancel,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.addRightCancel,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.addLeftComm,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.negNeg,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.negZero,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.addNegEqOfEqAdd,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.eqAddOfEqNegAdd,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.negAddDistrib,
  Foundations.Algebra.AdditiveCommutativeGroupLaws.negAddAddLeft,
  Foundations.Algebra.MultiplicativeCommutativeMonoidLaws.oneMul,
  Foundations.Algebra.MultiplicativeCommutativeMonoidLaws.mulLeftComm,
  Foundations.Algebra.CommutativeSemiringLaws.mulZero,
  Foundations.Algebra.CommutativeSemiringLaws.addMul
]

#audit_registered_claims

#audit_package [Foundations.Algebra] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
