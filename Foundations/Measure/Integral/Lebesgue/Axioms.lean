import Foundations.Measure.Integral.Lebesgue
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Measure.eq_iff_lintegral,
  Foundations.Measure.lintegral_comap,
  Foundations.Measure.lintegral_comap_of_zero_outside,
  Foundations.Measure.lintegral_smul_measure,
  Foundations.Measure.lintegral_piecewise,
  Foundations.Measure.lintegral_sub,
  Foundations.Measure.lintegral_sub_ae,
  Foundations.Measure.lintegral_iInf,
  Foundations.Measure.lintegral_iInf_ae,
  Foundations.Measure.SimpleFunction.integral_le_lintegral,
  Foundations.Measure.lintegral_le,
  Foundations.Measure.SimpleFunction.lintegral_eq_integral,
  Foundations.Measure.SimpleFunction.integral_eq_lintegral,
  Foundations.Measure.lintegral_mono,
  Foundations.Measure.lintegral_congr,
  Foundations.Measure.lintegral_mono_ae,
  Foundations.Measure.lintegral_congr_ae,
  Foundations.Measure.lintegral_eq_zero_of_ae_zero,
  Foundations.Measure.lintegral_iSup,
  Foundations.Measure.lintegral_eq_iSup_canonical,
  Foundations.Measure.lintegral_const,
  Foundations.Measure.lintegral_zero,
  Foundations.Measure.lintegral_indicator,
  Foundations.Measure.lintegral_add,
  Foundations.Measure.lintegral_smul,
  Foundations.Measure.lintegral_tsum,
  Foundations.Measure.lintegral_mono_measure,
  Foundations.Measure.lintegral_zero_measure,
  Foundations.Measure.lintegral_add_measure,
  Foundations.Measure.lintegral_sum_measure,
  Foundations.Measure.lintegral_sum,
  Foundations.Measure.lintegral_map,
  Foundations.Measure.lintegral_dirac,
  Foundations.Measure.upperLevel_measurable,
  Foundations.Measure.markov,
  Foundations.Measure.null_upperLevel_of_lintegral_eq_zero,
  Foundations.Measure.ae_zero_of_lintegral_eq_zero,
  Foundations.Measure.lintegral_eq_zero_iff
]

#audit_registered_claims

#audit_package [Foundations.Measure.Integral.Lebesgue] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
