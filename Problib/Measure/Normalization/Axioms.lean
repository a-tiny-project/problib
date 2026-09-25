import Problib.Measure.Normalization
import Problib.Measure.Normalization.Integral
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Measure.IsNormalizable,
  Problib.Measure.Measure.zero_not_normalizable,
  Problib.Measure.Measure.infinite_not_normalizable,
  Problib.Measure.Measure.IsNormalizable.of_finite_mass,
  Problib.Measure.Measure.normalize,
  Problib.Measure.Measure.normalize_eq_of_total_eq,
  Problib.Measure.Measure.normalize_congr,
  Problib.Measure.Measure.normalize_isProbability,
  Problib.Measure.Measure.smul_normalize,
  Problib.Measure.Measure.normalize_eq_of_smul_eq,
  Problib.Measure.Measure.IsProbability.to_normalizable,
  Problib.Measure.Measure.normalize_eq_self,
  Problib.Measure.Measure.IsNormalizable.map,
  Problib.Measure.Measure.normalize_map,
  Problib.Measure.Measure.isNormalizable_iff_probability_scaling,
  Problib.Measure.normalize_hasRealIntegral
]

#audit_registered_claims

#audit_package [Problib.Measure.Normalization] allowing [propext, Quot.sound, Classical.choice]
