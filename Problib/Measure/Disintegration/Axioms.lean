import Problib.Measure.Disintegration
import Problib.Measure.Disintegration.Pushforward
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Measure.Disintegration.conditional_isDensity,
  Problib.Measure.Measure.Disintegration.conditional_apply_aeEq,
  Problib.Measure.Measure.Disintegration.ae_eq,
  Problib.Measure.Measure.infinitePartCompatible_iff,
  Problib.Measure.Measure.Disintegration.smul,
  Problib.Measure.Measure.Disintegration.restrict,
  Problib.Measure.Measure.Disintegration.piecewise,
  Problib.Measure.Measure.Disintegration.piecewise_isProbability_ae,
  Problib.Measure.Measure.Disintegration.infinitePartCompatible,
  Problib.Measure.Measure.Disintegration.ofZeroInfinity,
  Problib.Measure.Measure.Disintegration.ofZeroInfinity_univ_le_one,
  Problib.Measure.Measure.Disintegration.ofZeroInfinity_isFinite,
  Problib.Measure.Measure.Disintegration.ofZeroInfinity_isProbability_ae,
  Problib.Measure.Measure.Disintegration.ofSFinite,
  Problib.Measure.Measure.Disintegration.ofSFinite_univ_le_one,
  Problib.Measure.Measure.Disintegration.ofSFinite_isFinite,
  Problib.Measure.Measure.Disintegration.ofSFinite_isProbability_ae,
  Problib.Measure.Measure.Disintegration.ofSFiniteProbability,
  Problib.Measure.Measure.Disintegration.ofSFiniteProbability_isProbability,
  Problib.Measure.Measure.Disintegration.nonempty_iff_infinitePartCompatible,
  Problib.Measure.Measure.Disintegration.comap,
  Problib.Measure.Measure.Disintegration.isProbability_ae,
  Problib.Measure.Measure.Disintegration.probabilityVersion,
  Problib.Measure.Measure.Disintegration.probabilityVersion_isProbability,
  Problib.Measure.Measure.Disintegration.probabilityVersion_aeEq,
  Problib.Measure.Measure.Disintegration.ofStandardBorel,
  Problib.Measure.Measure.Disintegration.ofStandardBorel_univ_le_one,
  Problib.Measure.Measure.Disintegration.ofStandardBorel_isFinite,
  Problib.Measure.Measure.Disintegration.ofStandardBorelProbability,
  Problib.Measure.Measure.Disintegration.ofStandardBorelProbability_isProbability,
  Problib.Measure.Measure.UnitDisintegration.initialMarginal,
  Problib.Measure.Measure.UnitDisintegration.initialMarginal_apply,
  Problib.Measure.Measure.UnitDisintegration.initialMarginal_le,
  Problib.Measure.Measure.UnitDisintegration.initialMarginal_mono,
  Problib.Measure.Measure.UnitDisintegration.initialMarginal_one,
  Problib.Measure.Measure.UnitDisintegration.conditional,
  Problib.Measure.Measure.UnitDisintegration.conditional_isProbability,
  Problib.Measure.Measure.UnitDisintegration.conditional_isFinite,
  Problib.Measure.Measure.UnitDisintegration.conditional_initial_le,
  Problib.Measure.Measure.UnitDisintegration.le_conditional_initial,
  Problib.Measure.Measure.UnitDisintegration.conditional_initial_of_finite,
  Problib.Measure.Measure.UnitDisintegration.conditional_reconstruct,
  Problib.Measure.Measure.UnitDisintegration.conditional_initial,
  Problib.Measure.Measure.Disintegration.ofUnit,
  Problib.Measure.Measure.Disintegration.ofUnit_isProbability,
  Problib.Measure.Measure.infinitePartMismatchSet_measurable,
  Problib.Measure.Measure.Disintegration.disintegrates,
  Problib.Measure.Measure.secondMarginal_graphJoint,
  Problib.Measure.Measure.lintegral_graphJoint,
  Problib.Measure.Measure.density_pushforward_of_disintegration,
  Problib.Measure.Measure.density_pushforward_normalized,
  Problib.Measure.Measure.density_reference_change,
  Problib.Measure.Measure.density_map_of_branches,
  Problib.Measure.Measure.density_map_translate
]

#audit_registered_claims

#audit_package [Problib.Measure.Disintegration,
  Problib.Measure.Disintegration.Pushforward] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
