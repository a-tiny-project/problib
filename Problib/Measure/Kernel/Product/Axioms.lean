import Problib.Measure.Kernel.Product
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Measure.semiproduct_smul,
  Problib.Measure.Measure.reverseSemiproduct_smul,
  Problib.Measure.Measure.semiproduct_restrict,
  Problib.Measure.Measure.reverseSemiproduct_restrict,
  Problib.Measure.Measure.semiproduct_piecewise,
  Problib.Measure.Measure.reverseSemiproduct_piecewise,
  Problib.Measure.Measure.semiproduct_congr_ae,
  Problib.Measure.Measure.reverseSemiproduct_congr_ae,
  Problib.Measure.Measure.reverseSemiproduct_apply_product,
  Problib.Measure.Kernel.pair_left_measurable,
  Problib.Measure.Kernel.attach_apply,
  Problib.Measure.Kernel.attach_zero,
  Problib.Measure.Kernel.attach_add,
  Problib.Measure.Kernel.attach_sum,
  Problib.Measure.Kernel.IsFinite.attach,
  Problib.Measure.Kernel.IsSFinite.attach,
  Problib.Measure.Measure.semiproduct_apply,
  Problib.Measure.Measure.semiproduct_apply_product,
  Problib.Measure.Measure.reverseSemiproduct_apply,
  Problib.Measure.Measure.prod_apply_product,
  Problib.Measure.Measure.prod_apply,
  Problib.Measure.Measure.prod_certificate_irrelevant,
  Problib.Measure.Measure.IsFinite.prod,
  Problib.Measure.Measure.prod_sum_left,
  Problib.Measure.Measure.prod_sum_right,
  Problib.Measure.Measure.prod_sum_both,
  Problib.Measure.Measure.SigmaFinite.prod,
  Problib.Measure.Measure.prod_unique,
  Problib.Measure.Measure.prod_swap_ofFinite,
  Problib.Measure.Measure.prod_swap,
  Problib.Measure.lintegral_semiproduct,
  Problib.Measure.Measure.semiproduct_withDensity_left,
  Problib.Measure.Measure.semiproduct_withDensity,
  Problib.Measure.lintegral_reverseSemiproduct,
  Problib.Measure.lintegral_prod,
  Problib.Measure.lintegral_prod_swap,
  Problib.Measure.lintegral_prod_symm,
  Problib.Measure.Measure.SFinite.semiproduct,
  Problib.Measure.Measure.SFinite.prod
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Product] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
