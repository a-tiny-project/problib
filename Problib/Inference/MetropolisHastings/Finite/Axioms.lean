import Problib.Inference.MetropolisHastings.Finite
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Inference.ProposalReach,
  Problib.Inference.mh_finite_minorization
]

#audit_registered_claims

#audit_package [Problib.Inference.MetropolisHastings.Finite] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
