import Problib.Measure.Kernel.Density
import Problib.Measure.Kernel.Density.Rules
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.jointly_measurable_slice,
  Problib.Measure.Kernel.withDensity_apply,
  Problib.Measure.Kernel.withDensity_apply_set,
  Problib.Measure.Kernel.lintegral_withDensity,
  Problib.Measure.Kernel.withDensity_congr,
  Problib.Measure.Kernel.withDensity_sum,
  Problib.Measure.Kernel.withDensity_tsum,
  Problib.Measure.Kernel.IsFinite.withDensity_of_bounded,
  Problib.Measure.Kernel.IsFinite.withDensity,
  Problib.Measure.Kernel.IsSFinite.withDensity,
  Problib.Measure.Kernel.densityReturn,
  Problib.Measure.Kernel.densityReturnAtom,
  Problib.Measure.Kernel.densityBind,
  Problib.Measure.Kernel.density_score,
  Problib.Measure.Kernel.density_normalize,
  Problib.Measure.Kernel.density_superpose,
  Problib.Measure.Kernel.density_product_two,
  Problib.Measure.Kernel.density_mem_of_limit,
  Problib.Measure.Kernel.densityLoop,
  Problib.Measure.Kernel.density_recur_of_increments
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Density,
  Problib.Measure.Kernel.Density.Rules] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
