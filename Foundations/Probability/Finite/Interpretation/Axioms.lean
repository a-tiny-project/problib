import Foundations.Probability.Finite.Interpretation
import Foundations.Probability.NNRat.Real.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Probability.FiniteMeasure.toMeasure,
  Foundations.Probability.FiniteMeasure.toMeasure_zero,
  Foundations.Probability.FiniteMeasure.toMeasure_cons,
  Foundations.Probability.FiniteMeasure.toMeasure_dirac,
  Foundations.Probability.FiniteMeasure.toMeasure_add,
  Foundations.Probability.FiniteMeasure.toMeasure_scale,
  Foundations.Probability.FiniteMeasure.toMeasure_univ,
  Foundations.Probability.FiniteMeasure.toMeasure_isFinite,
  Foundations.Probability.FiniteMeasure.toMeasure_isProbability,
  Foundations.Probability.FiniteMeasure.toMeasure_map,
  Foundations.Probability.FiniteMeasure.toMeasure_bind,
  Foundations.Probability.FiniteMeasure.toMeasure_apply,
  Foundations.Probability.FiniteMeasure.toMeasure_eq_of_equivalent,
  Foundations.Probability.FiniteMeasure.toMeasure_isNormalizable,
  Foundations.Probability.FiniteMeasure.toMeasure_normalize
]

#audit_registered_claims

#audit_package [Foundations.Probability.Finite.Interpretation] allowing [propext, Quot.sound, Classical.choice]
