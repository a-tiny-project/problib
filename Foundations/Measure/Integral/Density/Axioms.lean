import Foundations.Measure.Integral.Density
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Measure.withDensity_withDensity,
  Foundations.Measure.Measure.IsDensity.le_of_unit,
  Foundations.Measure.Measure.IsDensity.unit_ae_le_iff,
  Foundations.Measure.Measure.ae_zero_iff_of_withDensity_eq,
  Foundations.Measure.Measure.withDensity_apply_eq_zero_iff,
  Foundations.Measure.Measure.withDensity_finite_of_bounded,
  Foundations.Measure.Measure.withDensity_sigmaFinite_restrict_ne_top,
  Foundations.Measure.Measure.withDensity_add,
  Foundations.Measure.Measure.withDensity_indicator,
  Foundations.Measure.Measure.withDensity_piecewise,
  Foundations.Measure.Measure.withDensity_max,
  Foundations.Measure.Measure.withDensity_iSup_apply,
  Foundations.Measure.Measure.withDensity_tsum,
  Foundations.Measure.Measure.IsSubdensity.zero,
  Foundations.Measure.Measure.IsSubdensity.max,
  Foundations.Measure.Measure.IsSubdensity.prefixMax,
  Foundations.Measure.Measure.IsSubdensity.iSup,
  Foundations.Measure.Measure.IsSubdensity.toFinite,
  Foundations.Measure.Measure.IsSubdensity.exists_maximizer,
  Foundations.Measure.Measure.withDensity_apply,
  Foundations.Measure.Measure.isDensity_withDensity,
  Foundations.Measure.Measure.IsDensity.eq_withDensity,
  Foundations.Measure.Measure.IsDensity.apply,
  Foundations.Measure.Measure.IsDensity.ext,
  Foundations.Measure.Measure.withDensity_ext,
  Foundations.Measure.Measure.withDensity_congr_ae,
  Foundations.Measure.Measure.NullSet.withDensity,
  Foundations.Measure.Measure.AE.withDensity,
  Foundations.Measure.Measure.absolutelyContinuous_withDensity,
  Foundations.Measure.Measure.IsDensity.absolutelyContinuous,
  Foundations.Measure.lintegral_withDensity,
  Foundations.Measure.Measure.withDensity_mono_ae,
  Foundations.Measure.Measure.withDensity_restrict,
  Foundations.Measure.Measure.withDensity_const,
  Foundations.Measure.Measure.withDensity_zero,
  Foundations.Measure.Measure.withDensity_one,
  Foundations.Measure.Measure.withDensity_eq_zero_iff,
  Foundations.Measure.Measure.ae_le_of_withDensity_le_finite,
  Foundations.Measure.Measure.ae_le_of_withDensity_le,
  Foundations.Measure.Measure.withDensity_le_iff_ae_le,
  Foundations.Measure.Measure.ae_eq_of_withDensity_eq,
  Foundations.Measure.Measure.withDensity_eq_iff_ae_eq,
  Foundations.Measure.Measure.IsDensity.ae_eq
]

#audit_registered_claims

#audit_package [Foundations.Measure.Integral.Density] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
