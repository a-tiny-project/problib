import Foundations.Measure.StandardBorel
import Foundations.Measure.StandardBorel.Real.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.StandardBorel.ae_eq_of_apply_ae_eq,
  Foundations.Measure.StandardBorel.embedding,
  Foundations.Measure.StandardBorel.embeddingReal,
  Foundations.Measure.StandardBorel.embedding_range,
  Foundations.Measure.StandardBorel.ofEmbedding,
  Foundations.Measure.StandardBorel.ofRealLeftInverse,
  Foundations.Measure.StandardBorel.unitSquare,
  Foundations.Measure.StandardBorel.product,
  Foundations.Measure.StandardBorel.realPair,
  Foundations.Measure.StandardBorel.RealPair.encode,
  Foundations.Measure.StandardBorel.RealPair.decode,
  Foundations.Measure.StandardBorel.RealPair.decode_encode,
  Foundations.Measure.StandardBorel.RealPair.encode_measurable,
  Foundations.Measure.StandardBorel.RealPair.decode_measurable,
  Foundations.Measure.StandardBorel.RealPair.encode_injective,
  Foundations.Measure.StandardBorel.RealPair.range_measurable,
  Foundations.Measure.StandardBorel.ofUnitIntervalSet,
  Foundations.Measure.StandardBorel.unitInterval,
  Foundations.Measure.StandardBorel.naturalCode_injective,
  Foundations.Measure.StandardBorel.ofNatInjection,
  Foundations.Measure.StandardBorel.natural,
  Foundations.Measure.StandardBorel.unit
]

#audit_registered_claims

#audit_package [Foundations.Measure.StandardBorel] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
