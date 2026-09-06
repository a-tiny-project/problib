import Foundations.Measure.Uniform
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Real.uniform01_singleton,
  Foundations.Measure.Real.uniform01_strict_initial,
  Foundations.Measure.Real.unitThreshold_measurable,
  Foundations.Measure.Real.uniform01_threshold_true,
  Foundations.Measure.Real.restrictedUnit_univ,
  Foundations.Measure.Real.restrictedUnit_isProbability,
  Foundations.Measure.Real.uniform01_univ,
  Foundations.Measure.Real.uniform01_isProbability,
  Foundations.Measure.Real.uniform01_map_unitInclusion,
  Foundations.Measure.Real.uniform01_unitInitial
]

#audit_registered_claims

#audit_package [Foundations.Measure.Uniform] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
