import Problib.Real.Grind
import Trust.Command

open Problib.Real.Construction.Dedekind in
/-- An importer that does not open `Problib.Real.Grind` has no notation on the
carrier, and `real_grind` still closes an explicit-operation goal. -/
example (left right : selection.Carrier) :
    add (mul left right) (neg (mul right left)) = zero := by
  fail_if_success have := left + right
  real_grind

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.Grind.zero_eq,
  Problib.Real.Grind.one_eq,
  Problib.Real.Grind.commRing,
  Problib.Real.Grind.field,
  Problib.Real.Grind.characteristic,
  Problib.Real.Grind.linearOrder,
  Problib.Real.Grind.lawfulLT,
  Problib.Real.Grind.orderedRing,
  Problib.Real.Grind.add_eq,
  Problib.Real.Grind.mul_eq,
  Problib.Real.Grind.neg_eq,
  Problib.Real.Grind.sub_eq,
  Problib.Real.Grind.inverse_eq,
  Problib.Real.Grind.div_eq,
  Problib.Real.Grind.le_eq,
  Problib.Real.Grind.lt_eq,
  Problib.Real.Grind.ofRat_ofNat
]

#audit_registered_claims

#audit_package [Problib.Real.Grind] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
