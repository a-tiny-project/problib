import Foundations.Real.Nonnegative
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.NNReal.ext,
  Foundations.Real.NNReal.linearOrder,
  Foundations.Real.NNReal.semiring,
  Foundations.Real.NNReal.zeroLe,
  Foundations.Real.NNReal.zeroLtIffNeZero,
  Foundations.Real.NNReal.addLeAdd,
  Foundations.Real.NNReal.mulLeMul,
  Foundations.Real.NNReal.addEqZeroIff,
  Foundations.Real.NNReal.mulEqZeroIff,
  Foundations.Real.NNReal.ofRealOfNonnegative,
  Foundations.Real.NNReal.toRealOfReal,
  Foundations.Real.NNReal.ofRealMonotone,
  Foundations.Real.NNReal.ofRealEqZeroIff,
  Foundations.Real.NNReal.ofRatLeIff,
  Foundations.Real.NNReal.ofRatLtIff,
  Foundations.Real.NNReal.ofRatAdd,
  Foundations.Real.NNReal.ofRatMul,
  Foundations.Real.NNReal.existsRationalBetween,
  Foundations.Real.NNReal.mulLeftCancel,
  Foundations.Real.NNReal.mulRightCancel,
  Foundations.Real.NNReal.subAddCancel,
  Foundations.Real.NNReal.subEqZeroIffLe,
  Foundations.Real.NNReal.subLeIffLeAdd,
  Foundations.Real.NNReal.leSubIffAddLe,
  Foundations.Real.NNReal.divMulCancel,
  Foundations.Real.NNReal.mulDivCancel,
  Foundations.Real.NNReal.divSelf,
  Foundations.Real.NNReal.halfPositive,
  Foundations.Real.NNReal.halfAddHalf,
  Foundations.Real.NNReal.halfLe,
  Foundations.Real.NNReal.halfLt,
  Foundations.Real.NNReal.dyadic,
  Foundations.Real.NNReal.dyadicPositive,
  Foundations.Real.NNReal.dyadicStep,
  Foundations.Real.NNReal.dyadicAntitone,
  Foundations.Real.NNReal.leOfForallPositiveLeAdd,
  Foundations.Real.NNReal.existsSup,
  Foundations.Real.NNReal.supUpper,
  Foundations.Real.NNReal.leSup,
  Foundations.Real.NNReal.supLeast,
  Foundations.Real.NNReal.addSup,
  Foundations.Real.NNReal.mulSup
]

#audit_registered_claims

#audit_package [Foundations.Real.Nonnegative] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
