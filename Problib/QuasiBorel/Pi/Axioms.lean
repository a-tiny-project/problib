import Problib.QuasiBorel.Pi
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.QuasiBorel.Space.pi,
  Problib.QuasiBorel.Space.project,
  Problib.QuasiBorel.Space.tuple,
  Problib.QuasiBorel.Space.project_tuple,
  Problib.QuasiBorel.Space.tuple_project,
  Problib.QuasiBorel.Space.tuple_unique
]

#audit_registered_claims

#audit_package [Problib.QuasiBorel.Pi] allowing [propext, Quot.sound, Classical.choice]
