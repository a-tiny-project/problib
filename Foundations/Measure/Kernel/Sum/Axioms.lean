import Foundations.Measure.Kernel.Sum
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.copair,
  Foundations.Measure.Kernel.copair_inl,
  Foundations.Measure.Kernel.copair_inr,
  Foundations.Measure.Kernel.sum_ext,
  Foundations.Measure.Kernel.copair_unique,
  Foundations.Measure.Kernel.copair_precomp_inl,
  Foundations.Measure.Kernel.copair_precomp_inr,
  Foundations.Measure.Kernel.copair_eta,
  Foundations.Measure.Kernel.copair_sum,
  Foundations.Measure.Kernel.copair_map,
  Foundations.Measure.Kernel.IsFinite.copair,
  Foundations.Measure.Kernel.isFinite_copair_iff,
  Foundations.Measure.Kernel.IsSFinite.copair
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Sum] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
