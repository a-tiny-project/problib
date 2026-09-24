import Problib.Probability.Finite.Interpretation
import Problib.Probability.Finite.Interpretation.Rows
import Problib.Probability.NNRat.Real.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Probability.FiniteMeasure.toMeasure,
  Problib.Probability.FiniteMeasure.toMeasure_zero,
  Problib.Probability.FiniteMeasure.toMeasure_cons,
  Problib.Probability.FiniteMeasure.toMeasure_dirac,
  Problib.Probability.FiniteMeasure.toMeasure_add,
  Problib.Probability.FiniteMeasure.toMeasure_scale,
  Problib.Probability.FiniteMeasure.toMeasure_univ,
  Problib.Probability.FiniteMeasure.toMeasure_isFinite,
  Problib.Probability.FiniteMeasure.toMeasure_isProbability,
  Problib.Probability.FiniteMeasure.toMeasure_map,
  Problib.Probability.FiniteMeasure.toMeasure_bind,
  Problib.Probability.FiniteMeasure.toMeasure_apply,
  Problib.Probability.FiniteMeasure.toMeasure_eq_of_equivalent,
  Problib.Probability.FiniteMeasure.toMeasure_isNormalizable,
  Problib.Probability.FiniteMeasure.toMeasure_normalize,
  Problib.Probability.FiniteMeasure.toMeasure_normalize_map,
  Problib.Probability.FiniteMeasure.lintegral_toMeasure_map,
  Problib.Probability.FiniteMeasure.lintegral_toMeasure_map_of_singleton,
  Problib.Probability.FiniteMeasure.lintegral_toMeasure
]

#audit_registered_claims

#audit_package [Problib.Probability.Finite.Interpretation,
  Problib.Probability.Finite.Interpretation.Rows] allowing [propext, Quot.sound, Classical.choice]
