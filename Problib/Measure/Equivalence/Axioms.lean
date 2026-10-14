import Problib.Measure.Equivalence
import Problib.Measure.Equivalence.Partial
import Problib.Measure.Equivalence.Preserving
import Problib.Measure.Equivalence.Fibred
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.MeasurablePartialEquivalence,
  Problib.Measure.MeasurablePartialEquivalence.symm,
  Problib.Measure.MeasurablePartialEquivalence.trans,
  Problib.Measure.MeasurablePartialEquivalence.productRight,
  Problib.Measure.MeasurablePartialEquivalence.ofEquivalence,
  Problib.Measure.MeasurablePartialEquivalence.ReferenceChange,
  Problib.Measure.MeasurablePartialEquivalence.reference_change_symm,
  Problib.Measure.MeasurablePartialEquivalence.reference_change_trans,
  Problib.Measure.MeasurablePartialEquivalence.reference_change_productRight,
  Problib.Measure.MeasurableEquivalence.identity,
  Problib.Measure.MeasurableEquivalence.forward_injective,
  Problib.Measure.MeasurableEquivalence.inverse_injective,
  Problib.Measure.MeasurableEquivalence.symm,
  Problib.Measure.MeasurableEquivalence.trans,
  Problib.Measure.Measure.ext_of_lintegral,
  Problib.Measure.MeasurableEquivalence.product,
  Problib.Measure.MeasurableEquivalence.associate,
  Problib.Measure.MeasurableEquivalence.swap,
  Problib.Measure.MeasurableEquivalence.commuteLeft,
  Problib.Measure.MeasurableEquivalence.commuteRight,
  Problib.Measure.MeasurePreserving,
  Problib.Measure.MeasurePreserving.refl,
  Problib.Measure.MeasurePreserving.trans,
  Problib.Measure.MeasurePreserving.symm,
  Problib.Measure.MeasurePreserving.congr,
  Problib.Measure.MeasurePreserving.associate,
  Problib.Measure.MeasurePreserving.commuteLeft,
  Problib.Measure.MeasurePreserving.commuteRight,
  Problib.Measure.MeasurePreserving.reference_change_before,
  Problib.Measure.MeasurePreserving.reference_change_after,
  Problib.Measure.MeasurePreserving.swap,
  Problib.Measure.MeasurePreserving.product,
  Problib.Measure.MeasurePreserving.cast,
  Problib.Measure.MeasurePreserving.interchange,
  Problib.Measure.MeasurePreserving.fibre,
  Problib.Measure.MeasurePreserving.reference_change,
  Problib.Measure.MeasurablePartialEquivalence.reference_change_congr,
  Problib.Measure.MeasurablePartialEquivalence.fibred,
  Problib.Measure.MeasurablePartialEquivalence.reference_change_fibred,
  Problib.Measure.MeasurablePartialEquivalence.productLeft,
  Problib.Measure.MeasurablePartialEquivalence.reference_change_productLeft
]

#audit_registered_claims

#audit_package [Problib.Measure.Equivalence] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
