import Foundations.Measure.Kernel.Precomp
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.precomp,
  Foundations.Measure.Kernel.precomp_apply,
  Foundations.Measure.Kernel.precomp_id,
  Foundations.Measure.Kernel.precomp_comp,
  Foundations.Measure.Kernel.precomp_sum,
  Foundations.Measure.Kernel.precomp_map,
  Foundations.Measure.Kernel.IsFinite.precomp,
  Foundations.Measure.Kernel.IsSFinite.precomp
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Precomp] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
