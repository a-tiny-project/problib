import Foundations.Real.Inverse
import Foundations.Real.Inverse.Necessity
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.Construction.Dedekind.Cut.existsSelectedPositiveInverse,
  Foundations.Real.Construction.Dedekind.mulPositiveInverse,
  Foundations.Real.Construction.Dedekind.inverseZero,
  Foundations.Real.Construction.Dedekind.oneNeZero,
  Foundations.Real.Construction.Dedekind.mulInverseCancel,
  Foundations.Real.Construction.Dedekind.inverseMulCancel,
  Foundations.Real.Construction.Dedekind.inverseNonzero,
  Foundations.Real.Construction.Dedekind.mulEqZeroIff,
  Foundations.Real.Construction.Dedekind.mulLeftCancelOfNonzero,
  Foundations.Real.Construction.Dedekind.mulRightCancelOfNonzero,
  Foundations.Real.Construction.Dedekind.inverseInverse,
  Foundations.Real.Construction.Dedekind.inverseLtInverseOfPositive,
  Foundations.Real.Construction.Dedekind.inverseLeInverseOfPositive,
  Foundations.Real.Construction.Dedekind.divEqMulInverse,
  Foundations.Real.Construction.Dedekind.divNonnegative,
  Foundations.Real.Construction.Dedekind.divPositive,
  Foundations.Real.Construction.Dedekind.divLeDivOfPositive,
  Foundations.Real.Construction.Dedekind.divLtDivOfPositive,
  Foundations.Real.Construction.Dedekind.divMulCancel,
  Foundations.Real.Construction.Dedekind.mulDivCancel,
  Foundations.Real.Construction.Dedekind.divSelf,
  Foundations.Real.Construction.Dedekind.inverseOne,
  Foundations.Real.Construction.Dedekind.divOne,
  Foundations.Real.Construction.Dedekind.zeroDiv,
  Foundations.Real.Construction.Dedekind.divZero,
  Foundations.Real.Construction.Dedekind.divDivCancel,
  Foundations.Real.Inverse.Necessity.zero_numerator_does_not_cancel,
  Foundations.Real.Inverse.Necessity.nonnegative_is_insufficient_for_inverse_order
]

#audit_registered_claims

#audit_package [Foundations.Real.Inverse] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
