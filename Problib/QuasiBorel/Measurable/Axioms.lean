import Problib.QuasiBorel.Measurable
import Problib.QuasiBorel.Measurable.StandardBorel
import Problib.QuasiBorel.Measurable.Pair
import Problib.QuasiBorel.Measurable.Family
import Problib.QuasiBorel.Measurable.Necessity
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.QuasiBorel.SumRandom.measurable,
  Problib.QuasiBorel.Space.toMeasurable_initial,
  Problib.QuasiBorel.Space.toMeasurable_sum,
  Problib.QuasiBorel.Space.inlEmbedding,
  Problib.QuasiBorel.Space.inrEmbedding,
  Problib.QuasiBorel.Space.inlEmbedding_apply,
  Problib.QuasiBorel.Space.inrEmbedding_apply,
  Problib.QuasiBorel.Space.piToMeasurable,
  Problib.QuasiBorel.Space.piOfMeasurable,
  Problib.QuasiBorel.Space.piToMeasurable_piOfMeasurable,
  Problib.QuasiBorel.Space.piOfMeasurable_piToMeasurable,
  Problib.QuasiBorel.Source.ofMeasurable,
  Problib.QuasiBorel.Space.ofMeasurable,
  Problib.QuasiBorel.Hom.ofMeasurable,
  Problib.QuasiBorel.Hom.ofMeasurable_identity,
  Problib.QuasiBorel.Hom.ofMeasurable_comp,
  Problib.QuasiBorel.Hom.ofMeasurable_faithful,
  Problib.QuasiBorel.Space.toMeasurable,
  Problib.QuasiBorel.Space.random_measurable,
  Problib.QuasiBorel.RandomFamily.select_measurable,
  Problib.QuasiBorel.RandomFamily.join_select,
  Problib.QuasiBorel.RandomFamily.join_random,
  Problib.QuasiBorel.Space.pairRandom_encode,
  Problib.QuasiBorel.Space.pairRandom_accepted,
  Problib.QuasiBorel.Space.random_pair_measurable,
  Problib.QuasiBorel.Hom.toMeasurable,
  Problib.QuasiBorel.Space.measurableMap_iff_random,
  Problib.QuasiBorel.Space.toMeasurable_of_embedding,
  Problib.QuasiBorel.Hom.toMeasurable_of_embedding,
  Problib.QuasiBorel.Hom.measurable_of_embedding,
  Problib.QuasiBorel.Hom.ofMeasurable_full_of_embedding,
  Problib.QuasiBorel.Space.toMeasurable_of_standardBorel,
  Problib.QuasiBorel.Hom.measurable_of_standardBorel,
  Problib.QuasiBorel.Hom.ofMeasurable_full_of_standardBorel,
  Problib.QuasiBorel.Space.toMeasurable_of_standardBorel_real,
  Problib.QuasiBorel.Hom.measurable_of_standardBorel_real,
  Problib.QuasiBorel.Hom.ofMeasurable_full_of_standardBorel_real,
  Problib.QuasiBorel.Space.productToMeasurable,
  Problib.QuasiBorel.Space.productOfMeasurable,
  Problib.QuasiBorel.Space.productToMeasurable_productOfMeasurable,
  Problib.QuasiBorel.Space.productOfMeasurable_productToMeasurable,
  Problib.QuasiBorel.Hom.realPairEncode,
  Problib.QuasiBorel.Hom.realPairDecode,
  Problib.QuasiBorel.Hom.realPairDecode_realPairEncode,
  Problib.QuasiBorel.Necessity.singletonSourceHom,
  Problib.QuasiBorel.Necessity.singletonSourceHom_not_measurable
]

#audit_registered_claims

#audit_package [Problib.QuasiBorel.Measurable] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
