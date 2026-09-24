import Problib.Measure.TotalVariation
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Giry.Law.totalVariation,
  Problib.Measure.Giry.Law.event_sub_le,
  Problib.Measure.Giry.Law.totalVariation_le_one,
  Problib.Measure.Giry.Law.totalVariation_self,
  Problib.Measure.Giry.Law.totalVariation_symm,
  Problib.Measure.Giry.Law.totalVariation_eq_zero_iff,
  Problib.Measure.Giry.Law.totalVariation_triangle,
  Problib.Measure.Giry.Law.lintegral_sub_le_scaled_totalVariation,
  Problib.Measure.Giry.Law.lintegral_sub_le_totalVariation,
  Problib.Measure.Giry.Law.lintegral_distance_le_totalVariation,
  Problib.Measure.Giry.Law.totalVariation_eq_sup_lintegral
]

#audit_registered_claims

#audit_package [Problib.Measure.TotalVariation] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
