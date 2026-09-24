import Problib.Real
import Problib.Real.Additive.Axioms
import Problib.Real.Approximation.Axioms
import Problib.Real.Arithmetic
import Problib.Real.Basis.Axioms
import Problib.Real.Coding.Axioms
import Problib.Real.Extended.Axioms
import Problib.Real.Inverse.Axioms
import Problib.Real.Multiplicative.Axioms
import Problib.Real.Nonnegative.Axioms
import Problib.Real.Series.Axioms
import Problib.Real.Construction.Dedekind.AdditiveSelection.Axioms
import Problib.Real.Construction.Dedekind.MultiplicativeSelection.Axioms
import Problib.Real.Construction.Dedekind.Selection.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Real.Necessity.no_greatest_premise_necessary,
  Problib.Real.Necessity.order_embedding_need_not_preserve_addition,
  Problib.Real.Necessity.additive_group_and_order_need_not_translate_monotonically,
  Problib.Real.Necessity.multiplication_preservation_need_not_preserve_one,
  Problib.Real.DedekindComplete.exists_glb,
  Problib.Real.Construction.Dedekind.le_of_lt,
  Problib.Real.Construction.Dedekind.lt_trans,
  Problib.Real.Construction.Dedekind.lt_of_lt_of_le,
  Problib.Real.Construction.Dedekind.lt_of_le_of_lt,
  Problib.Real.Construction.Dedekind.lt_of_not_le,
  Problib.Real.Construction.Dedekind.not_le_of_lt,
  Problib.Real.Construction.Dedekind.lt_trichotomy,
  Problib.Real.Construction.Dedekind.lt_or_lt_of_ne,
  Problib.Real.Construction.Dedekind.add_lt_add_right,
  Problib.Real.Construction.Dedekind.add_lt_add_left,
  Problib.Real.Construction.Dedekind.add_le_add,
  Problib.Real.Construction.Dedekind.add_lt_add_le,
  Problib.Real.Construction.Dedekind.add_lt_add,
  Problib.Real.Construction.Dedekind.add_positive,
  Problib.Real.Construction.Dedekind.mul_neg,
  Problib.Real.Construction.Dedekind.neg_mul,
  Problib.Real.Construction.Dedekind.add_mul,
  Problib.Real.Construction.Dedekind.mul_sub,
  Problib.Real.Construction.Dedekind.sub_mul,
  Problib.Real.Construction.Dedekind.mul_zero,
  Problib.Real.Construction.Dedekind.zero_mul,
  Problib.Real.Construction.Dedekind.one_mul,
  Problib.Real.Construction.Dedekind.sub_self,
  Problib.Real.Construction.Dedekind.sub_zero,
  Problib.Real.Construction.Dedekind.sub_add_sub,
  Problib.Real.Construction.Dedekind.add_sub_cancel,
  Problib.Real.Construction.Dedekind.sub_add_cancel,
  Problib.Real.Construction.Dedekind.add_sub_self,
  Problib.Real.Construction.Dedekind.add_div,
  Problib.Real.Construction.Dedekind.sub_div,
  Problib.Real.Construction.Dedekind.mul_div_assoc,
  Problib.Real.Construction.Dedekind.div_mul_right,
  Problib.Real.Construction.Dedekind.neg_div,
  Problib.Real.Construction.Dedekind.inverse_mul,
  Problib.Real.Construction.Dedekind.inverse_sub,
  Problib.Real.Construction.Dedekind.one_positive,
  Problib.Real.Construction.Dedekind.neg_mul_neg,
  Problib.Real.Construction.Dedekind.neg_nonnegative_iff,
  Problib.Real.Construction.Dedekind.neg_positive_iff,
  Problib.Real.Construction.Dedekind.neg_negative_iff,
  Problib.Real.Construction.Dedekind.neg_nonpositive_iff,
  Problib.Real.Construction.Dedekind.neg_add,
  Problib.Real.Construction.Dedekind.neg_sub,
  Problib.Real.Construction.Dedekind.neg_sub_distrib,
  Problib.Real.Construction.Dedekind.sub_positive_iff,
  Problib.Real.Construction.Dedekind.small_positive,
  Problib.Real.Construction.Dedekind.inverse_neg,
  Problib.Real.Construction.Dedekind.ofRat_two_positive,
  Problib.Real.Construction.Dedekind.ofRat_succ_positive,
  Problib.Real.Construction.Dedekind.nonzero_of_positive,
  Problib.Real.Construction.Dedekind.ofRat_two_nonzero,
  Problib.Real.Construction.Dedekind.one_add_one,
  Problib.Real.Construction.Dedekind.le_of_equal,
  Problib.Real.Construction.Dedekind.le_of_not_le,
  Problib.Real.Construction.Dedekind.zero_add,
  Problib.Real.Construction.Dedekind.zero_sub,
  Problib.Real.Construction.Dedekind.sub_sub_cancel,
  Problib.Real.Construction.Dedekind.add_sub_add_comm,
  Problib.Real.Construction.Dedekind.sub_nonnegative,
  Problib.Real.Construction.Dedekind.add_nonnegative,
  Problib.Real.Construction.Dedekind.mul_self_nonnegative,
  Problib.Real.Construction.Dedekind.mul_mul_mul_comm,
  Problib.Real.Construction.Dedekind.inverse_mul_total,
  Problib.Real.Construction.Dedekind.mul_le_mul_left_iff,
  Problib.Real.Construction.Dedekind.mul_lt_mul_left_iff,
  Problib.Real.Construction.Dedekind.div_le_div_right
]

#audit_registered_claims

#audit_package [Problib.Real] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
