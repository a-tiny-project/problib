import Problib.Real.Additive.Axioms
import Problib.Real.Construction.Dedekind.AdditiveSelection
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.Construction.Dedekind.sub_eq_add_neg,
  Problib.Real.Construction.Dedekind.add_comm,
  Problib.Real.Construction.Dedekind.add_assoc,
  Problib.Real.Construction.Dedekind.add_left_comm,
  Problib.Real.Construction.Dedekind.add_zero,
  Problib.Real.Construction.Dedekind.add_neg,
  Problib.Real.Construction.Dedekind.add_left_cancel,
  Problib.Real.Construction.Dedekind.add_right_cancel,
  Problib.Real.Construction.Dedekind.ofRat_zero,
  Problib.Real.Construction.Dedekind.ofRat_add,
  Problib.Real.Construction.Dedekind.ofRat_neg,
  Problib.Real.Construction.Dedekind.ofRat_sub,
  Problib.Real.Construction.Dedekind.add_le_add_right_iff,
  Problib.Real.Construction.Dedekind.add_le_add_left_iff,
  Problib.Real.Construction.Dedekind.add_lt_add_right_iff,
  Problib.Real.Construction.Dedekind.add_lt_add_left_iff,
  Problib.Real.Construction.Dedekind.neg_le_neg_iff,
  Problib.Real.Construction.Dedekind.neg_lt_neg_iff
]

#audit_registered_claims

#audit_package [Problib.Real.Construction.Dedekind.AdditiveSelection]
  allowing [propext, Quot.sound, Classical.choice]
