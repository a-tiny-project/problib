import Foundations.Measure.Kernel.Product
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Measure.semiproduct_smul,
  Foundations.Measure.Measure.reverseSemiproduct_smul,
  Foundations.Measure.Measure.semiproduct_restrict,
  Foundations.Measure.Measure.reverseSemiproduct_restrict,
  Foundations.Measure.Measure.semiproduct_piecewise,
  Foundations.Measure.Measure.reverseSemiproduct_piecewise,
  Foundations.Measure.Measure.semiproduct_congr_ae,
  Foundations.Measure.Measure.reverseSemiproduct_congr_ae,
  Foundations.Measure.Measure.reverseSemiproduct_apply_product,
  Foundations.Measure.Kernel.pair_left_measurable,
  Foundations.Measure.Kernel.attach_apply,
  Foundations.Measure.Kernel.IsFinite.attach,
  Foundations.Measure.Kernel.IsSFinite.attach,
  Foundations.Measure.Measure.semiproduct_apply,
  Foundations.Measure.Measure.semiproduct_apply_product,
  Foundations.Measure.Measure.reverseSemiproduct_apply,
  Foundations.Measure.Measure.prod_apply_product,
  Foundations.Measure.Measure.prod_apply,
  Foundations.Measure.Measure.prod_certificate_irrelevant,
  Foundations.Measure.Measure.IsFinite.prod,
  Foundations.Measure.Measure.prod_sum_left,
  Foundations.Measure.Measure.prod_sum_right,
  Foundations.Measure.Measure.prod_sum_both,
  Foundations.Measure.Measure.SigmaFinite.prod,
  Foundations.Measure.Measure.prod_unique,
  Foundations.Measure.Measure.prod_swap_of_finite,
  Foundations.Measure.Measure.prod_swap,
  Foundations.Measure.lintegral_semiproduct,
  Foundations.Measure.lintegral_reverseSemiproduct,
  Foundations.Measure.lintegral_prod,
  Foundations.Measure.lintegral_prod_swap,
  Foundations.Measure.lintegral_prod_symm,
  Foundations.Measure.Measure.SFinite.semiproduct,
  Foundations.Measure.Measure.SFinite.prod
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Product] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
