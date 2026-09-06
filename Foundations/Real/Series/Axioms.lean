import Foundations.Real.Series
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.ENNReal.existsSequenceSupremum,
  Foundations.Real.ENNReal.prefixMax,
  Foundations.Real.ENNReal.prefixMaxStep,
  Foundations.Real.ENNReal.lePrefixMax,
  Foundations.Real.ENNReal.prefixMaxLeISup,
  Foundations.Real.ENNReal.iSupPrefixMax,
  Foundations.Real.ENNReal.tsumSubAdd,
  Foundations.Real.ENNReal.tsumSub,
  Foundations.Real.ENNReal.partialSumAppend,
  Foundations.Real.ENNReal.partialSumAddTail,
  Foundations.Real.ENNReal.tailLeTsum,
  Foundations.Real.ENNReal.tailAntitone,
  Foundations.Real.ENNReal.iInfTailEqZero,
  Foundations.Real.ENNReal.partialSumStep,
  Foundations.Real.ENNReal.partialSumMonotone,
  Foundations.Real.ENNReal.partialSumLeTsum,
  Foundations.Real.ENNReal.tsumLe,
  Foundations.Real.ENNReal.tsumLeastUpperBound,
  Foundations.Real.ENNReal.tsumZero,
  Foundations.Real.ENNReal.tsumLeTsum,
  Foundations.Real.ENNReal.tsumSingle,
  Foundations.Real.ENNReal.tsumEqZeroIff,
  Foundations.Real.ENNReal.tsumAdd,
  Foundations.Real.ENNReal.tsumMulLeft,
  Foundations.Real.ENNReal.tsumConstOfNeZero,
  Foundations.Real.ENNReal.tsumComm,
  Foundations.Real.ENNReal.tsumISup,
  Foundations.Real.NatProductBijection.encodeDecode,
  Foundations.Real.NatProductBijection.decodeEncode,
  Foundations.Real.ENNReal.tsumReindex,
  Foundations.Real.ENNReal.tsumFlatten,
  Foundations.Real.ENNReal.existsPositiveSummableError,
  Foundations.Real.ENNReal.rationalBasisFinite,
  Foundations.Real.ENNReal.existsRationalBasis,
  Foundations.Real.ENNReal.existsRationalBasisBetween,
  Foundations.Real.ENNReal.approximationFinite,
  Foundations.Real.ENNReal.approximationStep,
  Foundations.Real.ENNReal.approximationLe,
  Foundations.Real.ENNReal.iSupApproximation
]

#audit_registered_claims

#audit_package [Foundations.Real.Series] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
