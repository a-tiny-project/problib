import Foundations.Measure.Embedding
import Foundations.Measure.Embedding.Necessity
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.MeasurableEmbedding.retract,
  Foundations.Measure.MeasurableEmbedding.retract_forward,
  Foundations.Measure.MeasurableEmbedding.retract_measurable,
  Foundations.Measure.MeasurableEmbedding.ext,
  Foundations.Measure.MeasurableEmbedding.identity,
  Foundations.Measure.MeasurableEmbedding.trans,
  Foundations.Measure.MeasurableEmbedding.identity_trans,
  Foundations.Measure.MeasurableEmbedding.trans_identity,
  Foundations.Measure.MeasurableEmbedding.trans_assoc,
  Foundations.Measure.MeasurableEmbedding.range_measurable,
  Foundations.Measure.MeasurableEmbedding.ofLeftInverse,
  Foundations.Measure.MeasurableEmbedding.rangeEquivalence,
  Foundations.Measure.MeasurableEmbedding.product,
  Foundations.Measure.MeasurableEmbedding.product_range,
  Foundations.Measure.Embedding.Necessity.measurable_leftInverse_does_not_force_measurable_range,
  Foundations.Measure.MeasurableEmbedding.subtype,
  Foundations.Measure.MeasurableEmbedding.subtype_range,
  Foundations.Measure.MeasurableEquivalence.image_forward,
  Foundations.Measure.MeasurableEquivalence.toEmbedding,
  Foundations.Measure.MeasurableEquivalence.toEmbedding_range
]

#audit_registered_claims

#audit_package [Foundations.Measure.Embedding] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
