import Foundations.Real.Construction.Dedekind.Selection
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.Construction.Dedekind.leRefl,
  Foundations.Real.Construction.Dedekind.leTrans,
  Foundations.Real.Construction.Dedekind.leAntisymm,
  Foundations.Real.Construction.Dedekind.leTotal,
  Foundations.Real.Construction.Dedekind.ofRatLeIff,
  Foundations.Real.Construction.Dedekind.ofRatLtIff,
  Foundations.Real.Construction.Dedekind.ofRatInjective,
  Foundations.Real.Construction.Dedekind.existsLub,
  Foundations.Real.Construction.Dedekind.existsRationalBetween,
  Foundations.Real.Construction.Dedekind.existsNatUpper,
  Foundations.Real.Construction.Dedekind.existsNatStrictUpper
]

#audit_registered_claims

#audit_package [Foundations.Real.Construction.Dedekind.Selection] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
