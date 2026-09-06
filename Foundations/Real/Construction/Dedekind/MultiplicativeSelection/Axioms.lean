import Foundations.Real.Construction.Dedekind.MultiplicativeSelection
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.Construction.Dedekind.mulComm,
  Foundations.Real.Construction.Dedekind.mulAssoc,
  Foundations.Real.Construction.Dedekind.mulOne,
  Foundations.Real.Construction.Dedekind.mulAdd,
  Foundations.Real.Construction.Dedekind.mulNonnegative,
  Foundations.Real.Construction.Dedekind.oneNonnegative,
  Foundations.Real.Construction.Dedekind.mulLeMulNonnegativeRight,
  Foundations.Real.Construction.Dedekind.mulLeMulNonnegativeLeft,
  Foundations.Real.Construction.Dedekind.ofRatOne,
  Foundations.Real.Construction.Dedekind.ofRatMul
]

#audit_registered_claims

#audit_package [Foundations.Real.Construction.Dedekind.MultiplicativeSelection]
  allowing [propext, Quot.sound, Classical.choice]
