import Problib.Measure.Memo
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Memo.Indexed.law_probability,
  Problib.Measure.Memo.Indexed.law_coordinate_true,
  Problib.Measure.Memo.Indexed.ofBody_coordinate,
  Problib.Measure.Memo.Indexed.lazy_eq_table,
  Problib.Measure.Memo.Indexed.pair_true,
  Problib.Measure.Memo.Indexed.encoding_independent,
  Problib.Measure.Memo.Sparse.encode_run,
  Problib.Measure.Memo.Cell.mass_branch,
  Problib.Measure.Memo.decode_measurable,
  Problib.Measure.Memo.law_probability,
  Problib.Measure.Memo.law_prefix,
  Problib.Measure.Memo.law_cylinder,
  Problib.Measure.Memo.kernel_apply,
  Problib.Measure.Memo.Cache.weight_insert,
  Problib.Measure.Memo.Query.law_region,
  Problib.Measure.Memo.Query.lazy_eq_table,
  Problib.Measure.Memo.Query.lazy_congr,
  Problib.Measure.Memo.Sparse.run_check,
  Problib.Measure.Memo.Indexed.law_entries,
  Problib.Measure.Memo.Indexed.law_isProduct,
  Problib.Measure.Memo.Indexed.ofBody_isProduct,
  Problib.Measure.Memo.Indexed.ofBody_eq_pi,
  Problib.Measure.Memo.law_isProduct,
  Problib.Measure.Memo.binaryValue_measurable,
  Problib.Measure.Memo.binaryValue_decode,
  Problib.Measure.Memo.law_fair_binaryValue,
  Problib.Measure.Memo.rows_isProduct,
  Problib.Measure.Memo.uniformSequence_isProduct
]

#audit_registered_claims

#audit_package [Problib.Measure.Memo] allowing [propext, Quot.sound, Classical.choice]
