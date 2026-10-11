import Problib.Real.Basis
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.Construction.Dedekind.rationalBasis,
  Problib.Real.Construction.Dedekind.exists_rationalBasis,
  Problib.Real.Construction.Dedekind.exists_rationalBasis_between
]

#audit_registered_claims

#audit_package [Problib.Real.Basis] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
