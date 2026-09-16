import Foundations.Measure.Kernel.Iteration
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.le,
  Foundations.Measure.Kernel.leAntisymm,
  Foundations.Measure.Kernel.comp_le_comp_right,
  Foundations.Measure.Kernel.comp_add_distrib,
  Foundations.Measure.Kernel.comp_sum_right,
  Foundations.Measure.Kernel.comp_sum_left,
  Foundations.Measure.Kernel.sum_split_head,
  Foundations.Measure.Kernel.iterate,
  Foundations.Measure.Kernel.iterate_succ_right,
  Foundations.Measure.Kernel.loop,
  Foundations.Measure.Kernel.prefixApproximant,
  Foundations.Measure.Kernel.stepApproximant,
  Foundations.Measure.Kernel.prefixApproximant_step_unfold,
  Foundations.Measure.Kernel.prefixApproximant_eq_stepApproximant,
  Foundations.Measure.Kernel.prefixApproximant_apply_measurable,
  Foundations.Measure.Kernel.prefixApproximant_monotone,
  Foundations.Measure.Kernel.prefixApproximant_le_loop,
  Foundations.Measure.Kernel.loop_eq_iSup_prefixApproximant,
  Foundations.Measure.Kernel.loop_unfold,
  Foundations.Measure.Kernel.loop_least,
  Foundations.Measure.Kernel.IsSFinite.iterate,
  Foundations.Measure.Kernel.IsSFinite.loop,
  Foundations.Measure.Kernel.loop_zero_exit,
  Foundations.Measure.Kernel.loop_immediate_exit,
  Foundations.Measure.Kernel.iterate_zero_step_succ,
  Foundations.Measure.Kernel.iterate_identity,
  Foundations.Measure.Kernel.pure_continuation_fixed,
  Foundations.Measure.Kernel.prefix_mass_recurrence,
  Foundations.Measure.Kernel.prefix_mass_le_one,
  Foundations.Measure.Kernel.prefix_mass_eq_one,
  Foundations.Measure.Kernel.loop_mass_le_one,
  Foundations.Measure.Kernel.loop_isFinite,
  Foundations.Measure.Kernel.substochastic_isFinite,
  Foundations.Measure.Kernel.iterate_mass_antitone,
  Foundations.Measure.Kernel.loop_mass_eq_one_sub_iInf,
  Foundations.Measure.Kernel.loop_mass_add_iInf_eq_one,
  Foundations.Measure.Kernel.loop_mass_one_iff,
  Foundations.Measure.Kernel.VanishingContinuation,
  Foundations.Measure.Kernel.loop_mass_one_everywhere_iff,
  Foundations.Measure.Kernel.loop_isProbability,
  Foundations.Measure.Kernel.Iteration.Necessity.zero_pair_substochastic,
  Foundations.Measure.Kernel.Iteration.Necessity.zero_pair_not_conservative,
  Foundations.Measure.Kernel.Iteration.Necessity.vanishing_continuation_without_output,
  Foundations.Measure.Kernel.Iteration.Necessity.unfolding_does_not_determine_output
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Iteration] allowing [
  propext,
  Quot.sound,
  Classical.choice
]

#print axioms Foundations.Measure.Kernel.loop_unfold
#print axioms Foundations.Measure.Kernel.loop_least
#print axioms Foundations.Measure.Kernel.IsSFinite.loop
#print axioms Foundations.Measure.Kernel.prefix_mass_le_one
#print axioms Foundations.Measure.Kernel.prefix_mass_eq_one
#print axioms Foundations.Measure.Kernel.loop_mass_one_iff
#print axioms Foundations.Measure.Kernel.Iteration.Necessity.vanishing_continuation_without_output
#print axioms Foundations.Measure.Kernel.Iteration.Necessity.unfolding_does_not_determine_output
