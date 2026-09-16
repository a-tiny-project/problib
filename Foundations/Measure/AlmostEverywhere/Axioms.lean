import Foundations.Measure.AlmostEverywhere
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Measure.AE.of_restrict,
  Foundations.Measure.Measure.NullSet.add,
  Foundations.Measure.Measure.AE.add,
  Foundations.Measure.Measure.restrict_congr_ae,
  Foundations.Measure.Measure.ae_of_forall,
  Foundations.Measure.Measure.AE.mono,
  Foundations.Measure.Measure.AE.and,
  Foundations.Measure.Measure.ae_and_iff,
  Foundations.Measure.Measure.ae_all_iff,
  Foundations.Measure.Measure.AE.exists_null_exception,
  Foundations.Measure.Measure.AEEq.refl,
  Foundations.Measure.Measure.AEEq.symm,
  Foundations.Measure.Measure.AEEq.trans,
  Foundations.Measure.Measure.AEEq.comp,
  Foundations.Measure.Measure.ae_congr,
  Foundations.Measure.Measure.NullSet.preimage_of_map,
  Foundations.Measure.Measure.AE.of_map,
  Foundations.Measure.Measure.ae_map_iff,
  Foundations.Measure.Measure.AE.restrict,
  Foundations.Measure.Measure.AEEq.restrict,
  Foundations.Measure.Measure.AEEq.of_map,
  Foundations.Measure.Measure.ae_restrict_mem,
  Foundations.Measure.Measure.NullSet.of_restrict_cover,
  Foundations.Measure.Measure.null_iff_forall_restrict,
  Foundations.Measure.Measure.AE.of_restrict_cover,
  Foundations.Measure.Measure.ae_iff_forall_restrict,
  Foundations.Measure.Measure.AEEq.of_restrict_cover
]

#audit_registered_claims

#audit_package [Foundations.Measure.AlmostEverywhere] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
