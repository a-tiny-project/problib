import Foundations.Measure.Distribution
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Real.DistributionFunction.ext,
  Foundations.Measure.Real.DistributionFunction.ofUpperBounds,
  Foundations.Measure.Real.DistributionFunction.ofUpperBounds_le,
  Foundations.Measure.Real.DistributionFunction.le_ofUpperBounds,
  Foundations.Measure.Real.DistributionFunction.ofUpperBounds_lt_iff,
  Foundations.Measure.Real.DistributionFunction.ofUpperBounds_mono,
  Foundations.Measure.Real.DistributionFunction.ofUpperBounds_of_inactive,
  Foundations.Measure.Real.DistributionFunction.ofUpperBounds_eq,
  Foundations.Measure.Real.DistributionFunction.ofUpperBounds_measurable,
  Foundations.Measure.Real.DistributionFunction.quantile_jointly_measurable,
  Foundations.Measure.Real.DistributionFunction.function_measurable,
  Foundations.Measure.Real.DistributionFunction.rightContinuous_bounds,
  Foundations.Measure.Real.DistributionFunction.existsQuantile,
  Foundations.Measure.Real.DistributionFunction.quantile_lower,
  Foundations.Measure.Real.DistributionFunction.quantile_greatest,
  Foundations.Measure.Real.DistributionFunction.quantile_member,
  Foundations.Measure.Real.DistributionFunction.quantile_le_iff,
  Foundations.Measure.Real.DistributionFunction.quantile_monotone,
  Foundations.Measure.Real.DistributionFunction.quantile_measurable,
  Foundations.Measure.Real.DistributionFunction.quantile_zero,
  Foundations.Measure.Real.DistributionFunction.measure_isProbability,
  Foundations.Measure.Real.DistributionFunction.measure_initial,
  Foundations.Measure.Real.DistributionFunction.measure_unique,
  Foundations.Measure.Real.DistributionFunction.atomZero_measure_initial_zero,
  Foundations.Measure.Real.DistributionFunction.atomZero_singleton,
  Foundations.Measure.Real.DistributionFunction.identity_quantile,
  Foundations.Measure.Real.DistributionFunction.identity_measure,
  Foundations.Measure.Real.DistributionFunction.atomZero_measure
]

#audit_registered_claims

#audit_package [Foundations.Measure.Distribution] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
