import Foundations.Measure.Normalization
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Measure.IsNormalizable,
  Foundations.Measure.Measure.zero_not_normalizable,
  Foundations.Measure.Measure.infinite_not_normalizable,
  Foundations.Measure.Measure.normalize,
  Foundations.Measure.Measure.normalize_eq_of_total_eq,
  Foundations.Measure.Measure.normalize_isProbability,
  Foundations.Measure.Measure.smul_normalize,
  Foundations.Measure.Measure.normalize_eq_of_smul_eq,
  Foundations.Measure.Measure.IsProbability.toNormalizable,
  Foundations.Measure.Measure.normalize_eq_self,
  Foundations.Measure.Measure.IsNormalizable.map,
  Foundations.Measure.Measure.normalize_map,
  Foundations.Measure.Measure.isNormalizable_iff_probability_scaling
]

#audit_registered_claims

#audit_package [Foundations.Measure.Normalization] allowing [propext, Quot.sound, Classical.choice]
