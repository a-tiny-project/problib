import Problib.Measure.Kernel.Precomp
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.precomp,
  Problib.Measure.Kernel.precomp_apply,
  Problib.Measure.Kernel.precomp_id,
  Problib.Measure.Kernel.precomp_comp,
  Problib.Measure.Kernel.precomp_sum,
  Problib.Measure.Kernel.precomp_map,
  Problib.Measure.Kernel.IsFinite.precomp,
  Problib.Measure.Kernel.IsSFinite.precomp
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Precomp] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
