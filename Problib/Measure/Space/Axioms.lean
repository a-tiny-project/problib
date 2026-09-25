import Problib.Measure.Space.Indicator
import Problib.Measure.Space
import Problib.Measure.Space.Countable
import Problib.Measure.Space.Algebra
import Problib.Measure.Space.Selection
import Problib.Measure.Space.Sum
import Problib.Measure.Space.SumProduct
import Problib.Measure.Space.List
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Space.distribute_sum_measurable,
  Problib.Measure.Space.sum,
  Problib.Measure.Space.sum_measurable_iff,
  Problib.Measure.MeasurableMap.inl,
  Problib.Measure.MeasurableMap.inr,
  Problib.Measure.MeasurableMap.from_sum_iff,
  Problib.Measure.MeasurableMap.sum_elim,
  Problib.Measure.MeasurableMap.sum_elim_iff,
  Problib.Measure.MeasurableMap.sum_map,
  Problib.Measure.Space.CountableGenerator.measurable,
  Problib.Measure.Space.CountableGenerator.comap,
  Problib.Measure.Space.CountableGenerator.algebra,
  Problib.Measure.Space.exists_measurable_selection,
  Problib.Measure.Space.i_union_of_nat_injection,
  Problib.Measure.boolIndicator_measurable,
  Problib.Measure.Space.comap_measurable_iff,
  Problib.Measure.Space.ext,
  Problib.Measure.Space.univ,
  Problib.Measure.Space.union,
  Problib.Measure.Space.inter,
  Problib.Measure.Space.difference,
  Problib.Measure.Space.iInter,
  Problib.Measure.Space.prefixUnion_measurable,
  Problib.Measure.Space.disjointed_measurable,
  Problib.Measure.Space.generated_contains,
  Problib.Measure.Space.generated_minimal,
  Problib.Measure.Space.discrete_measurable,
  Problib.Measure.Space.indiscrete_measurable_iff,
  Problib.Measure.MeasurableMap.identity,
  Problib.Measure.MeasurableMap.comp,
  Problib.Measure.MeasurableMap.into_generated,
  Problib.Measure.MeasurableMap.to_discrete,
  Problib.Measure.MeasurableMap.from_discrete,
  Problib.Measure.Space.comap_map,
  Problib.Measure.Space.comap_minimal,
  Problib.Measure.MeasurableMap.constant,
  Problib.Measure.MeasurableMap.countable_piecewise,
  Problib.Measure.Space.list,
  Problib.Measure.ListSpace.coordinate,
  Problib.Measure.ListSpace.Generators,
  Problib.Measure.ListSpace.length_measurable,
  Problib.Measure.ListSpace.coordinate_measurable,
  Problib.Measure.ListSpace.measurable,
  Problib.Measure.ListSpace.cons_measurable,
  Problib.Measure.ListSpace.tail_measurable,
  Problib.Measure.ListSpace.view,
  Problib.Measure.ListSpace.view_measurable,
  Problib.Measure.ListSpace.foldN,
  Problib.Measure.ListSpace.foldN_measurable,
  Problib.Measure.ListSpace.foldN_length,
  Problib.Measure.ListSpace.fold_measurable
]

#audit_registered_claims

#audit_package [Problib.Measure.Space] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
