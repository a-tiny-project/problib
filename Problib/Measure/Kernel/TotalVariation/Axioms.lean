import Problib.Measure.Kernel.TotalVariation
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.totalVariation_bind,
  Problib.Measure.Giry.Law.totalVariation_map,
  Problib.Measure.Giry.Law.totalVariation_bind_le
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.TotalVariation] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
