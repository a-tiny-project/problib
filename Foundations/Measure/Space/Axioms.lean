import Foundations.Measure.Space.Indicator
import Foundations.Measure.Space
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
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
