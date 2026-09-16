import Foundations.Real.Basis
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.Construction.Dedekind.rationalBasis,
  Foundations.Real.Construction.Dedekind.existsRationalBasis,
  Foundations.Real.Construction.Dedekind.existsRationalBasisBetween
]

#audit_registered_claims

#audit_package [Foundations.Real.Basis] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
