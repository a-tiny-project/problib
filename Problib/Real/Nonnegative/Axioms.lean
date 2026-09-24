import Problib.Real.Nonnegative
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.NNReal.ext,
  Problib.Real.NNReal.linearOrder,
  Problib.Real.NNReal.semiring,
  Problib.Real.NNReal.zero_le,
  Problib.Real.NNReal.zero_lt_iff_ne_zero,
  Problib.Real.NNReal.add_le_add,
  Problib.Real.NNReal.mul_le_mul,
  Problib.Real.NNReal.add_eq_zero_iff,
  Problib.Real.NNReal.mul_eq_zero_iff,
  Problib.Real.NNReal.ofReal_of_nonnegative,
  Problib.Real.NNReal.ofReal_toReal,
  Problib.Real.NNReal.toReal_ofReal,
  Problib.Real.NNReal.ofReal_monotone,
  Problib.Real.NNReal.ofReal_eq_zero_iff,
  Problib.Real.NNReal.ofRat_le_iff,
  Problib.Real.NNReal.ofRat_lt_iff,
  Problib.Real.NNReal.ofRat_add,
  Problib.Real.NNReal.ofRat_mul,
  Problib.Real.NNReal.ofReal_ofRat,
  Problib.Real.NNReal.exists_rational_between,
  Problib.Real.NNReal.mul_left_cancel,
  Problib.Real.NNReal.mul_right_cancel,
  Problib.Real.NNReal.sub_add_cancel,
  Problib.Real.NNReal.sub_eq_zero_iff_le,
  Problib.Real.NNReal.sub_le_iff_le_add,
  Problib.Real.NNReal.le_sub_iff_add_le,
  Problib.Real.NNReal.div_mul_cancel,
  Problib.Real.NNReal.mul_div_cancel,
  Problib.Real.NNReal.div_self,
  Problib.Real.NNReal.half_positive,
  Problib.Real.NNReal.half_add_half,
  Problib.Real.NNReal.half_le,
  Problib.Real.NNReal.half_lt,
  Problib.Real.NNReal.dyadic,
  Problib.Real.NNReal.dyadic_positive,
  Problib.Real.NNReal.dyadic_step,
  Problib.Real.NNReal.dyadic_antitone,
  Problib.Real.NNReal.le_of_forall_positive_le_add,
  Problib.Real.NNReal.exists_sup,
  Problib.Real.NNReal.sup_upper,
  Problib.Real.NNReal.le_sup,
  Problib.Real.NNReal.sup_least,
  Problib.Real.NNReal.add_sup,
  Problib.Real.NNReal.mul_sup
]

#audit_registered_claims

#audit_package [Problib.Real.Nonnegative] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
