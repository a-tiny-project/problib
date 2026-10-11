import Problib.Real.Inverse
import Problib.Real.Inverse.Necessity
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.Construction.Dedekind.Cut.exists_selected_positive_inverse,
  Problib.Real.Construction.Dedekind.mul_positiveInverse,
  Problib.Real.Construction.Dedekind.inverse_zero,
  Problib.Real.Construction.Dedekind.one_ne_zero,
  Problib.Real.Construction.Dedekind.mul_inverse_cancel,
  Problib.Real.Construction.Dedekind.inverse_mul_cancel,
  Problib.Real.Construction.Dedekind.inverse_nonzero,
  Problib.Real.Construction.Dedekind.mul_eq_zero_iff,
  Problib.Real.Construction.Dedekind.mul_left_cancel_of_nonzero,
  Problib.Real.Construction.Dedekind.mul_right_cancel_of_nonzero,
  Problib.Real.Construction.Dedekind.inverse_inverse,
  Problib.Real.Construction.Dedekind.inverse_lt_inverse_of_positive,
  Problib.Real.Construction.Dedekind.inverse_le_inverse_of_positive,
  Problib.Real.Construction.Dedekind.div_eq_mul_inverse,
  Problib.Real.Construction.Dedekind.div_nonnegative,
  Problib.Real.Construction.Dedekind.div_positive,
  Problib.Real.Construction.Dedekind.div_le_div_of_positive,
  Problib.Real.Construction.Dedekind.div_lt_div_of_positive,
  Problib.Real.Construction.Dedekind.div_mul_cancel,
  Problib.Real.Construction.Dedekind.mul_div_cancel,
  Problib.Real.Construction.Dedekind.div_self,
  Problib.Real.Construction.Dedekind.inverse_one,
  Problib.Real.Construction.Dedekind.div_one,
  Problib.Real.Construction.Dedekind.zero_div,
  Problib.Real.Construction.Dedekind.div_zero,
  Problib.Real.Construction.Dedekind.div_div_cancel,
  Problib.Real.Construction.Dedekind.ofRat_inverse,
  Problib.Real.Construction.Dedekind.ofRat_div,
  Problib.Real.Inverse.Necessity.zero_numerator_does_not_cancel,
  Problib.Real.Inverse.Necessity.nonnegative_is_insufficient_for_inverse_order
]

#audit_registered_claims

#audit_package [Problib.Real.Inverse] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
