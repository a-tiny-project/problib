import Problib.Measure.Kernel.Iteration
import Problib.Measure.Kernel.Iteration.Minorization.Axioms
import Problib.Measure.Kernel.Iteration.Finite.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.le,
  Problib.Measure.Kernel.le_antisymm,
  Problib.Measure.Kernel.comp_le_comp_right,
  Problib.Measure.Kernel.comp_le_comp_left,
  Problib.Measure.Kernel.comp_add_distrib,
  Problib.Measure.Kernel.add_comp_distrib,
  Problib.Measure.Kernel.comp_sum_right,
  Problib.Measure.Kernel.comp_sum_left,
  Problib.Measure.Kernel.sum_split_head,
  Problib.Measure.Kernel.iterate,
  Problib.Measure.Kernel.iterate_succ_right,
  Problib.Measure.Kernel.loop,
  Problib.Measure.Kernel.prefixApproximant,
  Problib.Measure.Kernel.stepApproximant,
  Problib.Measure.Kernel.prefixApproximant_step_unfold,
  Problib.Measure.Kernel.prefixApproximant_eq_stepApproximant,
  Problib.Measure.Kernel.prefixApproximant_apply_measurable,
  Problib.Measure.Kernel.prefixApproximant_monotone,
  Problib.Measure.Kernel.prefixApproximant_le_loop,
  Problib.Measure.Kernel.loop_eq_iSup_prefixApproximant,
  Problib.Measure.Kernel.loop_unfold,
  Problib.Measure.Kernel.loop_least,
  Problib.Measure.Kernel.IsSFinite.iterate,
  Problib.Measure.Kernel.IsSFinite.loop,
  Problib.Measure.Kernel.prefixApproximant_zero_exit,
  Problib.Measure.Kernel.boundedLoop,
  Problib.Measure.Kernel.boundedLoop_apply,
  Problib.Measure.Kernel.boundedLoop_exhausted,
  Problib.Measure.Kernel.boundedLoop_succeeded,
  Problib.Measure.Kernel.boundedLoop_zero,
  Problib.Measure.Kernel.boundedLoop_zero_exit,
  Problib.Measure.Kernel.boundedLoop_succ,
  Problib.Measure.Kernel.boundedLoop_isProbability,
  Problib.Measure.Kernel.loop_zero_exit,
  Problib.Measure.Kernel.loop_immediate_exit,
  Problib.Measure.Kernel.iterate_zero_step_succ,
  Problib.Measure.Kernel.iterate_identity,
  Problib.Measure.Kernel.pure_continuation_fixed,
  Problib.Measure.Kernel.prefix_mass_recurrence,
  Problib.Measure.Kernel.prefix_mass_le_one,
  Problib.Measure.Kernel.prefix_mass_eq_one,
  Problib.Measure.Kernel.loop_mass_le_one,
  Problib.Measure.Kernel.loop_isFinite,
  Problib.Measure.Kernel.substochastic_isFinite,
  Problib.Measure.Kernel.iterate_mass_antitone,
  Problib.Measure.Kernel.loop_mass_eq_one_sub_iInf,
  Problib.Measure.Kernel.loop_mass_add_iInf_eq_one,
  Problib.Measure.Kernel.loop_mass_one_iff,
  Problib.Measure.Kernel.VanishingContinuation,
  Problib.Measure.Kernel.loop_mass_one_everywhere_iff,
  Problib.Measure.Kernel.loop_isProbability,
  Problib.Measure.Kernel.Lumps,
  Problib.Measure.Kernel.iterate_map_of_lumps,
  Problib.Measure.Kernel.Iteration.Necessity.zero_pair_substochastic,
  Problib.Measure.Kernel.Iteration.Necessity.zero_pair_not_conservative,
  Problib.Measure.Kernel.Iteration.Necessity.vanishing_continuation_without_output,
  Problib.Measure.Kernel.Iteration.Necessity.unfolding_does_not_determine_output,
  Problib.Measure.Kernel.OmegaContinuous,
  Problib.Measure.Kernel.OmegaContinuous.linear,
  Problib.Measure.Kernel.fixedPointApproximant,
  Problib.Measure.Kernel.fixedPointApproximant_monotone,
  Problib.Measure.Kernel.leastFixedPoint,
  Problib.Measure.Kernel.leastFixedPoint_apply_measurable,
  Problib.Measure.Kernel.leastFixedPoint_unfold,
  Problib.Measure.Kernel.leastFixedPoint_least,
  Problib.Measure.Kernel.leastFixedPoint_linear_eq_loop,
  Problib.Measure.Kernel.IsSFinite.leastFixedPointOfPrefixSum
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Iteration] allowing [
  propext,
  Quot.sound,
  Classical.choice
]

#print axioms Problib.Measure.Kernel.loop_unfold
#print axioms Problib.Measure.Kernel.loop_least
#print axioms Problib.Measure.Kernel.IsSFinite.loop
#print axioms Problib.Measure.Kernel.prefix_mass_le_one
#print axioms Problib.Measure.Kernel.prefix_mass_eq_one
#print axioms Problib.Measure.Kernel.loop_mass_one_iff
#print axioms Problib.Measure.Kernel.Iteration.Necessity.vanishing_continuation_without_output
#print axioms Problib.Measure.Kernel.Iteration.Necessity.unfolding_does_not_determine_output
