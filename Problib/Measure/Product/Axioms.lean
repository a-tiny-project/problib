import Problib.Measure.Product.Generator
import Problib.Measure.Product.Countable
import Trust.Command
import Problib.Measure.Product.Selection

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Space.selected_set_measurable,
  Problib.Measure.MeasurableMap.uncurry_of_countable_first,
  Problib.Measure.MeasurableMap.uncurry_measurable_iff_of_countable_first,
  Problib.Measure.Space.rectangle_piSystem,
  Problib.Measure.Space.rectangle_contains_univ,
  Problib.Measure.Space.first_measurable,
  Problib.Measure.Space.second_measurable,
  Problib.Measure.Space.product_set_measurable,
  Problib.Measure.Space.rectangle_measurable,
  Problib.Measure.Space.product_eq_generated_rectangles,
  Problib.Measure.Space.pair_measurable,
  Problib.Measure.Space.pair_measurable_iff,
  Problib.Measure.Space.product_map,
  Problib.Measure.Space.swap_measurable,
  Problib.Measure.Space.associate_measurable,
  Problib.Measure.Space.unassociate_measurable
]

#audit_registered_claims

#audit_package [Problib.Measure.Product] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
