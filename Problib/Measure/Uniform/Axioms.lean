import Problib.Measure.Uniform
import Problib.Measure.Uniform.Band
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Real.uniform01_singleton,
  Problib.Measure.Real.uniform01_strict_initial,
  Problib.Measure.Real.unitThreshold_measurable,
  Problib.Measure.Real.uniform01_threshold_true,
  Problib.Measure.Real.restrictedUnit_univ,
  Problib.Measure.Real.restrictedUnit_isProbability,
  Problib.Measure.Real.uniform01_univ,
  Problib.Measure.Real.uniform01_isProbability,
  Problib.Measure.Real.uniform01_map_unitInclusion,
  Problib.Measure.Real.uniform01_unitInitial,
  Problib.Measure.Real.unitBand_measurable,
  Problib.Measure.Real.unitBand_empty,
  Problib.Measure.Real.uniform01_unitBand,
  Problib.Measure.Real.uniform01_real_initial_of_one_le
]

#audit_registered_claims

#audit_package [Problib.Measure.Uniform, Problib.Measure.Uniform.Band] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
