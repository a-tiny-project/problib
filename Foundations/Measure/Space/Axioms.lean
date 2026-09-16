import Foundations.Measure.Space.Indicator
import Foundations.Measure.Space
import Foundations.Measure.Space.Countable
import Foundations.Measure.Space.Algebra
import Foundations.Measure.Space.Selection
import Foundations.Measure.Space.Sum
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Space.sum,
  Foundations.Measure.Space.sum_measurable_iff,
  Foundations.Measure.MeasurableMap.inl,
  Foundations.Measure.MeasurableMap.inr,
  Foundations.Measure.MeasurableMap.fromSum_iff,
  Foundations.Measure.MeasurableMap.sumElim,
  Foundations.Measure.MeasurableMap.sumElim_iff,
  Foundations.Measure.MeasurableMap.sumMap,
  Foundations.Measure.Space.CountableGenerator.measurable,
  Foundations.Measure.Space.CountableGenerator.comap,
  Foundations.Measure.Space.CountableGenerator.algebra,
  Foundations.Measure.Space.exists_measurable_selection,
  Foundations.Measure.Space.iUnion_ofNatInjection,
  Foundations.Measure.boolIndicator_measurable,
  Foundations.Measure.Space.comap_measurable_iff,
  Foundations.Measure.Space.ext,
  Foundations.Measure.Space.univ,
  Foundations.Measure.Space.union,
  Foundations.Measure.Space.inter,
  Foundations.Measure.Space.difference,
  Foundations.Measure.Space.iInter,
  Foundations.Measure.Space.prefixUnion_measurable,
  Foundations.Measure.Space.disjointed_measurable,
  Foundations.Measure.Space.generated_contains,
  Foundations.Measure.Space.generated_minimal,
  Foundations.Measure.Space.discrete_measurable,
  Foundations.Measure.Space.indiscrete_measurable_iff,
  Foundations.Measure.MeasurableMap.identity,
  Foundations.Measure.MeasurableMap.comp,
  Foundations.Measure.MeasurableMap.intoGenerated,
  Foundations.Measure.MeasurableMap.toDiscrete,
  Foundations.Measure.MeasurableMap.fromDiscrete,
  Foundations.Measure.Space.comap_map,
  Foundations.Measure.Space.comap_minimal,
  Foundations.Measure.MeasurableMap.constant,
  Foundations.Measure.MeasurableMap.countablePiecewise
]

#audit_registered_claims

#audit_package [Foundations.Measure.Space] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
