import Foundations.QuasiBorel.Pi
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.QuasiBorel.Space.pi,
  Foundations.QuasiBorel.Space.project,
  Foundations.QuasiBorel.Space.tuple,
  Foundations.QuasiBorel.Space.project_tuple,
  Foundations.QuasiBorel.Space.tuple_project,
  Foundations.QuasiBorel.Space.tuple_unique
]

#audit_registered_claims

#audit_package [Foundations.QuasiBorel.Pi] allowing [propext, Quot.sound, Classical.choice]
