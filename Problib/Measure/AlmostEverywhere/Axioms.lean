import Problib.Measure.AlmostEverywhere
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Measure.AE.of_restrict,
  Problib.Measure.Measure.NullSet.add,
  Problib.Measure.Measure.AE.add,
  Problib.Measure.Measure.restrict_congr_ae,
  Problib.Measure.Measure.ae_of_forall,
  Problib.Measure.Measure.AE.mono,
  Problib.Measure.Measure.AE.and,
  Problib.Measure.Measure.ae_and_iff,
  Problib.Measure.Measure.ae_all_iff,
  Problib.Measure.Measure.AE.exists_null_exception,
  Problib.Measure.Measure.AEEq.refl,
  Problib.Measure.Measure.AEEq.symm,
  Problib.Measure.Measure.AEEq.trans,
  Problib.Measure.Measure.AEEq.comp,
  Problib.Measure.Measure.ae_congr,
  Problib.Measure.Measure.NullSet.preimage_of_map,
  Problib.Measure.Measure.AE.of_map,
  Problib.Measure.Measure.ae_map_iff,
  Problib.Measure.Measure.AE.restrict,
  Problib.Measure.Measure.AEEq.restrict,
  Problib.Measure.Measure.AEEq.of_map,
  Problib.Measure.Measure.ae_restrict_mem,
  Problib.Measure.Measure.NullSet.of_restrict_cover,
  Problib.Measure.Measure.null_iff_forall_restrict,
  Problib.Measure.Measure.AE.of_restrict_cover,
  Problib.Measure.Measure.ae_iff_forall_restrict,
  Problib.Measure.Measure.AEEq.of_restrict_cover
]

#audit_registered_claims

#audit_package [Problib.Measure.AlmostEverywhere] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
