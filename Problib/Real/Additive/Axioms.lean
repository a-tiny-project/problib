import Problib.Real.Additive
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.RationalAdditiveHomomorphism.map_zero,
  Problib.Real.RationalAdditiveHomomorphism.map_neg,
  Problib.Real.RationalAdditiveHomomorphism.map_sub
]

#audit_registered_claims

#audit_package [Problib.Real.Additive] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
