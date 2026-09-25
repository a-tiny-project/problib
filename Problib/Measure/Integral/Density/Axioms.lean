import Problib.Measure.Integral.Density
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Measure.withDensity_withDensity,
  Problib.Measure.Measure.IsDensity.le_of_unit,
  Problib.Measure.Measure.IsDensity.unit_ae_le_iff,
  Problib.Measure.Measure.ae_zero_iff_of_withDensity_eq,
  Problib.Measure.Measure.withDensity_apply_eq_zero_iff,
  Problib.Measure.Measure.withDensity_finite_of_bounded,
  Problib.Measure.Measure.withDensity_sigmaFinite_restrict_ne_top,
  Problib.Measure.Measure.withDensity_add,
  Problib.Measure.Measure.withDensity_indicator,
  Problib.Measure.Measure.withDensity_piecewise,
  Problib.Measure.Measure.withDensity_max,
  Problib.Measure.Measure.withDensity_iSup_apply,
  Problib.Measure.Measure.withDensity_tsum,
  Problib.Measure.Measure.IsSubdensity.zero,
  Problib.Measure.Measure.IsSubdensity.max,
  Problib.Measure.Measure.IsSubdensity.prefixMax,
  Problib.Measure.Measure.IsSubdensity.iSup,
  Problib.Measure.Measure.IsSubdensity.to_finite,
  Problib.Measure.Measure.IsSubdensity.exists_maximizer,
  Problib.Measure.Measure.withDensity_apply,
  Problib.Measure.Measure.isDensity_withDensity,
  Problib.Measure.Measure.IsDensity.eq_withDensity,
  Problib.Measure.Measure.IsDensity.apply,
  Problib.Measure.Measure.IsDensity.ext,
  Problib.Measure.Measure.withDensity_ext,
  Problib.Measure.Measure.withDensity_congr_ae,
  Problib.Measure.Measure.NullSet.withDensity,
  Problib.Measure.Measure.AE.withDensity,
  Problib.Measure.Measure.absolutelyContinuous_withDensity,
  Problib.Measure.Measure.IsDensity.absolutelyContinuous,
  Problib.Measure.lintegral_withDensity,
  Problib.Measure.Measure.map_withDensity,
  Problib.Measure.Measure.withDensity_mono_ae,
  Problib.Measure.Measure.withDensity_restrict,
  Problib.Measure.Measure.withDensity_const,
  Problib.Measure.Measure.withDensity_normalize,
  Problib.Measure.Measure.withDensity_zero,
  Problib.Measure.Measure.withDensity_one,
  Problib.Measure.Measure.withDensity_eq_zero_iff,
  Problib.Measure.Measure.ae_le_of_withDensity_le_finite,
  Problib.Measure.Measure.ae_le_of_withDensity_le,
  Problib.Measure.Measure.withDensity_le_iff_ae_le,
  Problib.Measure.Measure.aeEq_of_withDensity_eq,
  Problib.Measure.Measure.withDensity_eq_iff_aeEq,
  Problib.Measure.Measure.IsDensity.ae_eq,
  Problib.Measure.IntegralParts.ofWithDensity,
  Problib.Measure.HasRealIntegral.of_withDensity,
  Problib.Measure.densityRatio,
  Problib.Measure.mul_densityRatio,
  Problib.Measure.densityRatio_measurable,
  Problib.Measure.isDensity_densityRatio
]

#audit_registered_claims

#audit_package [Problib.Measure.Integral.Density] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
