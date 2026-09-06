import Foundations.QuasiBorel.Measurable
import Foundations.QuasiBorel.Measurable.StandardBorel
import Foundations.QuasiBorel.Measurable.Pair
import Foundations.QuasiBorel.Measurable.Necessity
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.QuasiBorel.Source.ofMeasurable,
  Foundations.QuasiBorel.Space.ofMeasurable,
  Foundations.QuasiBorel.Hom.ofMeasurable,
  Foundations.QuasiBorel.Hom.ofMeasurable_identity,
  Foundations.QuasiBorel.Hom.ofMeasurable_comp,
  Foundations.QuasiBorel.Hom.ofMeasurable_faithful,
  Foundations.QuasiBorel.Space.toMeasurable,
  Foundations.QuasiBorel.Hom.toMeasurable,
  Foundations.QuasiBorel.Space.measurableMap_iff_random,
  Foundations.QuasiBorel.Space.toMeasurable_ofEmbedding,
  Foundations.QuasiBorel.Hom.measurable_ofEmbedding,
  Foundations.QuasiBorel.Hom.ofMeasurable_full_ofEmbedding,
  Foundations.QuasiBorel.Space.toMeasurable_ofStandardBorel,
  Foundations.QuasiBorel.Hom.measurable_ofStandardBorel,
  Foundations.QuasiBorel.Hom.ofMeasurable_full_ofStandardBorel,
  Foundations.QuasiBorel.Space.toMeasurable_ofStandardBorelReal,
  Foundations.QuasiBorel.Hom.measurable_ofStandardBorelReal,
  Foundations.QuasiBorel.Hom.ofMeasurable_full_ofStandardBorelReal,
  Foundations.QuasiBorel.Space.productToMeasurable,
  Foundations.QuasiBorel.Space.productOfMeasurable,
  Foundations.QuasiBorel.Space.productToMeasurable_productOfMeasurable,
  Foundations.QuasiBorel.Space.productOfMeasurable_productToMeasurable,
  Foundations.QuasiBorel.Hom.realPairEncode,
  Foundations.QuasiBorel.Hom.realPairDecode,
  Foundations.QuasiBorel.Hom.realPairDecode_realPairEncode,
  Foundations.QuasiBorel.Necessity.singletonSourceHom,
  Foundations.QuasiBorel.Necessity.singletonSourceHom_not_measurable
]

#audit_registered_claims

#audit_package [Foundations.QuasiBorel.Measurable] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
