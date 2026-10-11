import Problib.Measure.Kernel.Iteration.Minorization
import Problib.Measure.Kernel.Iteration.Minorization.Composition
import Problib.Measure.Kernel.Iteration.Minorization.Necessity
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.Minorization,
  Problib.Measure.Kernel.MinorizationOn,
  Problib.Measure.Kernel.minorization_on_univ,
  Problib.Measure.Kernel.iterate_isProbability,
  Problib.Measure.Kernel.invariant_iterate,
  Problib.Measure.Kernel.iterate_add,
  Problib.Measure.Kernel.iterate_mul,
  Problib.Measure.Kernel.iterateLaw,
  Problib.Measure.Kernel.iterateLaw_zero,
  Problib.Measure.Kernel.iterateLaw_add,
  Problib.Measure.Kernel.iterateLaw_invariant,
  Problib.Measure.Kernel.minorization_block_contraction,
  Problib.Measure.Kernel.minorization_contraction,
  Problib.Measure.Kernel.minorization_decay_base_lt_one,
  Problib.Measure.Kernel.minorization_converges,
  Problib.Measure.Kernel.minorization_unique_invariant,
  Problib.Measure.Kernel.lawThrough,
  Problib.Measure.Kernel.minorization_on_comp_right,
  Problib.Measure.Kernel.minorization_comp_right,
  Problib.Measure.Kernel.minorization_on_of_entrance,
  Problib.Measure.Kernel.minorization_comp_left,
  Problib.Measure.Kernel.minorization_mixture,
  Problib.Measure.Kernel.mixtureBlockWeight,
  Problib.Measure.Kernel.mixtureBlockWeight_finite,
  Problib.Measure.Kernel.iterate_mixture_lower,
  Problib.Measure.Kernel.minorization_mixture_block,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.states,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.fair,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.fair_probability,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.averaging,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.averaging_fixed,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.averaging_moving,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.averaging_markov,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.cycle,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.reverse,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.reverse_markov,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.step,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.step_markov,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.step_moving,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.step_fixed,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.step_block_minorization,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.step_comp_reverse,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.averaging_not_minorized,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.count,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.step_invariant,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.reverse_invariant,
  Problib.Measure.Kernel.Iteration.Necessity.Interleaving.block_minorization_not_interleaved
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Iteration.Minorization] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
