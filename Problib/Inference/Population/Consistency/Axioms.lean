import Problib.Inference.Population.Consistency
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Inference.IndependentPair,
  Problib.Inference.hasRealIntegral_pair_mul,
  Problib.Inference.lane_variance,
  Problib.Inference.unnormalizedEstimate_measurable,
  Problib.Inference.WeightBounded,
  Problib.Inference.EmpiricalL2,
  Problib.Inference.PairwiseProduct,
  Problib.Inference.meanSquare_bind,
  Problib.Inference.propagation_l2,
  Problib.Inference.propagation_weight_bounded,
  Problib.Inference.lanewise_l2,
  Problib.Inference.lanewise_weight_bounded,
  Problib.Inference.IndependentAncestors,
  Problib.Inference.IndependentAncestors.marginal,
  Problib.Inference.IndependentAncestors.pair,
  Problib.Inference.multinomial_independent,
  Problib.Inference.resample_conditional,
  Problib.Inference.ResamplingError,
  Problib.Inference.resampling_error_of_independent,
  Problib.Inference.multinomial_resampling_error,
  Problib.Inference.resample_mean_of_invariant,
  Problib.Inference.resampling_l2,
  Problib.Inference.resampling_weight_bounded,
  Problib.Inference.initial_l2,
  Problib.Inference.initial_weight_bounded,
  Problib.Inference.estimate_consistent,
  Problib.Inference.population_consistent
]

#audit_registered_claims

#audit_package [Problib.Inference.Population.Consistency] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
