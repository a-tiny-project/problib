import Foundations.Real.Approximation
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.Construction.Dedekind.existsPositiveInverseBelow
]

#audit_registered_claims

#audit_package [Foundations.Real.Approximation] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
