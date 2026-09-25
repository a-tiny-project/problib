import Problib.Real.Construction.Dedekind.MultiplicativeSelection
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.Construction.Dedekind.mul_comm,
  Problib.Real.Construction.Dedekind.mul_assoc,
  Problib.Real.Construction.Dedekind.mul_one,
  Problib.Real.Construction.Dedekind.mul_add,
  Problib.Real.Construction.Dedekind.mul_nonnegative,
  Problib.Real.Construction.Dedekind.one_nonnegative,
  Problib.Real.Construction.Dedekind.mul_le_mul_nonnegative_right,
  Problib.Real.Construction.Dedekind.mul_le_mul_nonnegative_left,
  Problib.Real.Construction.Dedekind.ofRat_one,
  Problib.Real.Construction.Dedekind.ofRat_mul
]

#audit_registered_claims

#audit_package [Problib.Real.Construction.Dedekind.MultiplicativeSelection]
  allowing [propext, Quot.sound, Classical.choice]
