import Problib.Real.Approximation
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.Construction.Dedekind.exists_positive_inverse_below
]

#audit_registered_claims

#audit_package [Problib.Real.Approximation] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
