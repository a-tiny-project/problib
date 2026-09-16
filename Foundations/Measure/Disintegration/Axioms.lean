import Foundations.Measure.Disintegration
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Measure.Disintegration.conditional_isDensity,
  Foundations.Measure.Measure.Disintegration.conditional_apply_ae_eq,
  Foundations.Measure.Measure.Disintegration.ae_eq,
  Foundations.Measure.Measure.infinitePartCompatible_iff,
  Foundations.Measure.Measure.Disintegration.smul,
  Foundations.Measure.Measure.Disintegration.restrict,
  Foundations.Measure.Measure.Disintegration.piecewise,
  Foundations.Measure.Measure.Disintegration.piecewise_isProbability_ae,
  Foundations.Measure.Measure.Disintegration.infinitePartCompatible,
  Foundations.Measure.Measure.Disintegration.ofZeroInfinity,
  Foundations.Measure.Measure.Disintegration.ofZeroInfinity_univ_le_one,
  Foundations.Measure.Measure.Disintegration.ofZeroInfinity_isFinite,
  Foundations.Measure.Measure.Disintegration.ofZeroInfinity_isProbability_ae,
  Foundations.Measure.Measure.Disintegration.ofSFinite,
  Foundations.Measure.Measure.Disintegration.ofSFinite_univ_le_one,
  Foundations.Measure.Measure.Disintegration.ofSFinite_isFinite,
  Foundations.Measure.Measure.Disintegration.ofSFinite_isProbability_ae,
  Foundations.Measure.Measure.Disintegration.ofSFiniteProbability,
  Foundations.Measure.Measure.Disintegration.ofSFiniteProbability_isProbability,
  Foundations.Measure.Measure.Disintegration.nonempty_iff_infinitePartCompatible,
  Foundations.Measure.Measure.Disintegration.comap,
  Foundations.Measure.Measure.Disintegration.isProbability_ae,
  Foundations.Measure.Measure.Disintegration.probabilityVersion,
  Foundations.Measure.Measure.Disintegration.probabilityVersion_isProbability,
  Foundations.Measure.Measure.Disintegration.probabilityVersion_ae_eq,
  Foundations.Measure.Measure.Disintegration.ofStandardBorel,
  Foundations.Measure.Measure.Disintegration.ofStandardBorel_univ_le_one,
  Foundations.Measure.Measure.Disintegration.ofStandardBorel_isFinite,
  Foundations.Measure.Measure.Disintegration.ofStandardBorelProbability,
  Foundations.Measure.Measure.Disintegration.ofStandardBorelProbability_isProbability,
  Foundations.Measure.Measure.UnitDisintegration.initialMarginal,
  Foundations.Measure.Measure.UnitDisintegration.initialMarginal_apply,
  Foundations.Measure.Measure.UnitDisintegration.initialMarginal_le,
  Foundations.Measure.Measure.UnitDisintegration.initialMarginal_mono,
  Foundations.Measure.Measure.UnitDisintegration.initialMarginal_one,
  Foundations.Measure.Measure.UnitDisintegration.conditional,
  Foundations.Measure.Measure.UnitDisintegration.conditional_isProbability,
  Foundations.Measure.Measure.UnitDisintegration.conditional_isFinite,
  Foundations.Measure.Measure.UnitDisintegration.conditional_initial_le,
  Foundations.Measure.Measure.UnitDisintegration.le_conditional_initial,
  Foundations.Measure.Measure.UnitDisintegration.conditional_initial_of_finite,
  Foundations.Measure.Measure.UnitDisintegration.conditional_reconstruct,
  Foundations.Measure.Measure.UnitDisintegration.conditional_initial,
  Foundations.Measure.Measure.Disintegration.ofUnit,
  Foundations.Measure.Measure.Disintegration.ofUnit_isProbability,
  Foundations.Measure.Measure.infinitePartMismatchSet_measurable,
  Foundations.Measure.Measure.Disintegration.disintegrates
]

#audit_registered_claims

#audit_package [Foundations.Measure.Disintegration] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
