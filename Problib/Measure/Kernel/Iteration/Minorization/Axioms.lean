import Problib.Measure.Kernel.Iteration.Minorization
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.Minorization,
  Problib.Measure.Kernel.iterate_isProbability,
  Problib.Measure.Kernel.invariant_iterate,
  Problib.Measure.Kernel.iterate_add,
  Problib.Measure.Kernel.iterateLaw,
  Problib.Measure.Kernel.iterateLaw_zero,
  Problib.Measure.Kernel.iterateLaw_add,
  Problib.Measure.Kernel.iterateLaw_invariant,
  Problib.Measure.Kernel.minorization_block_contraction,
  Problib.Measure.Kernel.minorization_contraction,
  Problib.Measure.Kernel.minorization_converges,
  Problib.Measure.Kernel.minorization_unique_invariant
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Iteration.Minorization] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
