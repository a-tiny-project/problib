import Problib.Measure.Distribution
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Real.DistributionFunction.ext,
  Problib.Measure.Real.DistributionFunction.ofUpperBounds,
  Problib.Measure.Real.DistributionFunction.ofUpperBounds_le,
  Problib.Measure.Real.DistributionFunction.le_ofUpperBounds,
  Problib.Measure.Real.DistributionFunction.ofUpperBounds_lt_iff,
  Problib.Measure.Real.DistributionFunction.ofUpperBounds_mono,
  Problib.Measure.Real.DistributionFunction.ofUpperBounds_of_inactive,
  Problib.Measure.Real.DistributionFunction.ofUpperBounds_eq,
  Problib.Measure.Real.DistributionFunction.ofUpperBounds_measurable,
  Problib.Measure.Real.DistributionFunction.quantile_jointly_measurable,
  Problib.Measure.Real.DistributionFunction.function_measurable,
  Problib.Measure.Real.DistributionFunction.right_continuous_bounds,
  Problib.Measure.Real.DistributionFunction.exists_quantile,
  Problib.Measure.Real.DistributionFunction.quantile_lower,
  Problib.Measure.Real.DistributionFunction.quantile_greatest,
  Problib.Measure.Real.DistributionFunction.quantile_member,
  Problib.Measure.Real.DistributionFunction.quantile_le_iff,
  Problib.Measure.Real.DistributionFunction.quantile_monotone,
  Problib.Measure.Real.DistributionFunction.quantile_measurable,
  Problib.Measure.Real.DistributionFunction.quantile_zero,
  Problib.Measure.Real.DistributionFunction.measure_isProbability,
  Problib.Measure.Real.DistributionFunction.measure_initial,
  Problib.Measure.Real.DistributionFunction.measure_unique,
  Problib.Measure.Real.DistributionFunction.atomZero_measure_initial_zero,
  Problib.Measure.Real.DistributionFunction.atomZero_singleton,
  Problib.Measure.Real.DistributionFunction.identity_quantile,
  Problib.Measure.Real.DistributionFunction.identity_measure,
  Problib.Measure.Real.DistributionFunction.atomZero_measure
]

#audit_registered_claims

#audit_package [Problib.Measure.Distribution] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
