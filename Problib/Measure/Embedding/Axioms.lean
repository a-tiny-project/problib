import Problib.Measure.Embedding
import Problib.Measure.Embedding.Generator
import Problib.Measure.Embedding.Necessity
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.MeasurableEmbedding.inl,
  Problib.Measure.MeasurableEmbedding.inr,
  Problib.Measure.MeasurableEmbedding.inl_apply,
  Problib.Measure.MeasurableEmbedding.inr_apply,
  Problib.Measure.MeasurableEmbedding.countableGenerator,
  Problib.Measure.MeasurableEmbedding.retract,
  Problib.Measure.MeasurableEmbedding.retract_forward,
  Problib.Measure.MeasurableEmbedding.retract_measurable,
  Problib.Measure.MeasurableEmbedding.ext,
  Problib.Measure.MeasurableEmbedding.identity,
  Problib.Measure.MeasurableEmbedding.trans,
  Problib.Measure.MeasurableEmbedding.identity_trans,
  Problib.Measure.MeasurableEmbedding.trans_identity,
  Problib.Measure.MeasurableEmbedding.trans_assoc,
  Problib.Measure.MeasurableEmbedding.range_measurable,
  Problib.Measure.MeasurableEmbedding.ofLeftInverse,
  Problib.Measure.MeasurableEmbedding.rangeEquivalence,
  Problib.Measure.MeasurableEmbedding.product,
  Problib.Measure.MeasurableEmbedding.product_range,
  Problib.Measure.Embedding.Necessity.measurable_left_inverse_does_not_force_measurable_range,
  Problib.Measure.MeasurableEmbedding.subtype,
  Problib.Measure.MeasurableEmbedding.subtype_range,
  Problib.Measure.MeasurableEquivalence.image_forward,
  Problib.Measure.MeasurableEquivalence.toEmbedding,
  Problib.Measure.MeasurableEquivalence.toEmbedding_range
]

#audit_registered_claims

#audit_package [Problib.Measure.Embedding] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
