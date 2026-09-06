import Foundations.Real.Additive
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.RationalAdditiveHomomorphism.mapZero,
  Foundations.Real.RationalAdditiveHomomorphism.mapNeg,
  Foundations.Real.RationalAdditiveHomomorphism.mapSub
]

#audit_registered_claims

#audit_package [Foundations.Real.Additive] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
