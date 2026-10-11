import Problib.Measure.Kernel.Sum
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.copair,
  Problib.Measure.Kernel.copair_inl,
  Problib.Measure.Kernel.copair_inr,
  Problib.Measure.Kernel.sum_ext,
  Problib.Measure.Kernel.copair_unique,
  Problib.Measure.Kernel.copair_precomp_inl,
  Problib.Measure.Kernel.copair_precomp_inr,
  Problib.Measure.Kernel.copair_eta,
  Problib.Measure.Kernel.copair_sum,
  Problib.Measure.Kernel.copair_map,
  Problib.Measure.Kernel.IsFinite.copair,
  Problib.Measure.Kernel.isFinite_copair_iff,
  Problib.Measure.Kernel.IsSFinite.copair
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Sum] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
