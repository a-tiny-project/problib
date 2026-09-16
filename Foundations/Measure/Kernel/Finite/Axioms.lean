import Foundations.Measure.Kernel.Finite
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.IsSFinite.ofFiniteFibers
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Finite] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
