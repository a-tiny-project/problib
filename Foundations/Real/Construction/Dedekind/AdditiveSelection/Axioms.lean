import Foundations.Real.Additive.Axioms
import Foundations.Real.Construction.Dedekind.AdditiveSelection
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.Construction.Dedekind.subEqAddNeg,
  Foundations.Real.Construction.Dedekind.addComm,
  Foundations.Real.Construction.Dedekind.addAssoc,
  Foundations.Real.Construction.Dedekind.addLeftComm,
  Foundations.Real.Construction.Dedekind.addZero,
  Foundations.Real.Construction.Dedekind.addNeg,
  Foundations.Real.Construction.Dedekind.addLeftCancel,
  Foundations.Real.Construction.Dedekind.addRightCancel,
  Foundations.Real.Construction.Dedekind.ofRatZero,
  Foundations.Real.Construction.Dedekind.ofRatAdd,
  Foundations.Real.Construction.Dedekind.ofRatNeg,
  Foundations.Real.Construction.Dedekind.ofRatSub,
  Foundations.Real.Construction.Dedekind.addLeAddRightIff,
  Foundations.Real.Construction.Dedekind.addLeAddLeftIff,
  Foundations.Real.Construction.Dedekind.addLtAddRightIff,
  Foundations.Real.Construction.Dedekind.addLtAddLeftIff,
  Foundations.Real.Construction.Dedekind.negLeNegIff,
  Foundations.Real.Construction.Dedekind.negLtNegIff
]

#audit_registered_claims

#audit_package [Foundations.Real.Construction.Dedekind.AdditiveSelection]
  allowing [propext, Quot.sound, Classical.choice]
