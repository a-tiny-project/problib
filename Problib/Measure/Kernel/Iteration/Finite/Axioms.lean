import Problib.Measure.Kernel.Iteration.Finite
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.matrixSum,
  Problib.Measure.Kernel.matrixIterate,
  Problib.Measure.Kernel.positiveColumn,
  Problib.Measure.Kernel.positiveColumn_iff,
  Problib.Measure.Kernel.columnMin,
  Problib.Measure.Kernel.kernelColumnMin,
  Problib.Measure.Kernel.positive_column_minorization,
  Problib.Measure.Kernel.Irreducible,
  Problib.Measure.Kernel.Reaches,
  Problib.Measure.Kernel.AperiodicAt,
  Problib.Measure.Kernel.Aperiodic,
  Problib.Measure.Kernel.reaches_step,
  Problib.Measure.Kernel.reaches_refl,
  Problib.Measure.Kernel.aperiodicAt_of_hold,
  Problib.Measure.Kernel.finite_accessible_aperiodic_minorization,
  Problib.Measure.Kernel.finite_irreducible_aperiodic_minorization,
  Problib.Measure.Kernel.positiveColumn_sound,
  Problib.Measure.Kernel.positiveColumn_sound_exact,
  Problib.Measure.Kernel.TwoState.rows,
  Problib.Measure.Kernel.TwoState.halfWeight,
  Problib.Measure.Kernel.TwoState.law,
  Problib.Measure.Kernel.TwoState.kernel,
  Problib.Measure.Kernel.TwoState.positive_column,
  Problib.Measure.Kernel.TwoState.checked_minorization,
  Problib.Measure.Kernel.TwoState.explicit_rate
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Iteration.Finite] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
