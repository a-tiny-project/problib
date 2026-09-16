import Foundations.Measure.Product.Generator
import Foundations.Measure.Product.Countable
import Trust.Command
import Foundations.Measure.Product.Selection

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Space.selectedSet_measurable,
  Foundations.Measure.MeasurableMap.uncurry_ofCountableFirst,
  Foundations.Measure.MeasurableMap.uncurry_measurable_iff_ofCountableFirst,
  Foundations.Measure.Space.rectangle_piSystem,
  Foundations.Measure.Space.rectangle_contains_univ,
  Foundations.Measure.Space.first_measurable,
  Foundations.Measure.Space.second_measurable,
  Foundations.Measure.Space.product_set_measurable,
  Foundations.Measure.Space.rectangle_measurable,
  Foundations.Measure.Space.product_eq_generated_rectangles,
  Foundations.Measure.Space.pair_measurable,
  Foundations.Measure.Space.pair_measurable_iff,
  Foundations.Measure.Space.product_map,
  Foundations.Measure.Space.swap_measurable,
  Foundations.Measure.Space.associate_measurable,
  Foundations.Measure.Space.unassociate_measurable
]

#audit_registered_claims

#audit_package [Foundations.Measure.Product] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
