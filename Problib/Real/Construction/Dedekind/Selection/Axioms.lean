import Problib.Real.Construction.Dedekind.Selection
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.Construction.Dedekind.le_refl,
  Problib.Real.Construction.Dedekind.le_trans,
  Problib.Real.Construction.Dedekind.le_antisymm,
  Problib.Real.Construction.Dedekind.le_total,
  Problib.Real.Construction.Dedekind.ofRat_le_iff,
  Problib.Real.Construction.Dedekind.ofRat_lt_iff,
  Problib.Real.Construction.Dedekind.ofRat_injective,
  Problib.Real.Construction.Dedekind.exists_lub,
  Problib.Real.Construction.Dedekind.exists_rational_between,
  Problib.Real.Construction.Dedekind.exists_nat_upper,
  Problib.Real.Construction.Dedekind.exists_nat_strict_upper
]

#audit_registered_claims

#audit_package [Problib.Real.Construction.Dedekind.Selection] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
