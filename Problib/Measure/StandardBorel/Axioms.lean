import Problib.Measure.StandardBorel.Necessity
import Problib.Measure.StandardBorel
import Problib.Measure.StandardBorel.Real.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.StandardBorel.countableGenerator,
  Problib.Measure.StandardBorel.ofEmpty,
  Problib.Measure.StandardBorel.unitSequence,
  Problib.Measure.StandardBorel.piOfNatInjection,
  Problib.Measure.StandardBorel.countableProduct,
  Problib.Measure.StandardBorel.realSequence,
  Problib.Measure.StandardBorel.Necessity.booleanProduct,
  Problib.Measure.StandardBorel.Necessity.boolean_factors_standardBorel,
  Problib.Measure.StandardBorel.Necessity.booleanProduct_not_standardBorel,
  Problib.Measure.StandardBorel.Necessity.arbitrary_product_closure_fails,
  Problib.Measure.StandardBorel.Necessity.empty_index_product_standardBorel,
  Problib.Measure.StandardBorel.Necessity.countable_empty_product_standardBorel,
  Problib.Measure.StandardBorel.Necessity.countable_empty_product_empty,
  Problib.Measure.StandardBorel.aeEq_of_apply_aeEq,
  Problib.Measure.StandardBorel.embedding,
  Problib.Measure.StandardBorel.embeddingReal,
  Problib.Measure.StandardBorel.embedding_range,
  Problib.Measure.StandardBorel.ofEmbedding,
  Problib.Measure.StandardBorel.ofRealLeftInverse,
  Problib.Measure.StandardBorel.unitSquare,
  Problib.Measure.StandardBorel.product,
  Problib.Measure.StandardBorel.realPair,
  Problib.Measure.StandardBorel.RealPair.encode,
  Problib.Measure.StandardBorel.RealPair.decode,
  Problib.Measure.StandardBorel.RealPair.decode_encode,
  Problib.Measure.StandardBorel.RealPair.encode_measurable,
  Problib.Measure.StandardBorel.RealPair.decode_measurable,
  Problib.Measure.StandardBorel.RealPair.encode_injective,
  Problib.Measure.StandardBorel.RealPair.range_measurable,
  Problib.Measure.StandardBorel.ofUnitIntervalSet,
  Problib.Measure.StandardBorel.unitInterval,
  Problib.Measure.StandardBorel.naturalCode_injective,
  Problib.Measure.StandardBorel.ofNatInjection,
  Problib.Measure.StandardBorel.natural,
  Problib.Measure.StandardBorel.unit
]

#audit_registered_claims

#audit_package [Problib.Measure.StandardBorel] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
