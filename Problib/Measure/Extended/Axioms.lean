import Problib.Measure.Extended
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.ENNRealMeasurable.densityRatio,
  Problib.Measure.Real.unitRationalBasis,
  Problib.Measure.Real.exists_unitRationalBasis_between,
  Problib.Measure.Real.toReal_measurable,
  Problib.Measure.Real.unitClamp,
  Problib.Measure.Real.ofReal_unitClamp,
  Problib.Measure.Real.ofReal_unitClamp_of_le,
  Problib.Measure.Real.unitClamp_ofReal,
  Problib.Measure.Real.unitClamp_top,
  Problib.Measure.Real.unitClamp_mono,
  Problib.Measure.Real.unitClamp_measurable,
  Problib.Measure.ENNRealMeasurable.iInf,
  Problib.Measure.Real.ofReal_measurable,
  Problib.Measure.ENNRealMeasurable.max,
  Problib.Measure.ENNRealMeasurable.prefixMax,
  Problib.Measure.ennrealBorel_generator,
  Problib.Measure.ennrealBorel_minimal,
  Problib.Measure.ENNRealMeasurable.measurableMap,
  Problib.Measure.ENNRealMeasurable.of_measurableMap,
  Problib.Measure.ENNRealMeasurable.measurableMap_iff,
  Problib.Measure.ENNRealMeasurable.ioi,
  Problib.Measure.ENNRealMeasurable.constant,
  Problib.Measure.ENNRealMeasurable.identity,
  Problib.Measure.ENNRealMeasurable.comp,
  Problib.Measure.ENNRealMeasurable.piecewise,
  Problib.Measure.ENNRealMeasurable.indicator,
  Problib.Measure.ENNRealMeasurable.iic,
  Problib.Measure.ENNRealMeasurable.iio,
  Problib.Measure.ENNRealMeasurable.ici,
  Problib.Measure.ENNRealMeasurable.singleton,
  Problib.Measure.ENNRealMeasurable.lt_set,
  Problib.Measure.ENNRealMeasurable.le_set,
  Problib.Measure.ENNRealMeasurable.eq_set,
  Problib.Measure.ENNRealMeasurable.approximation,
  Problib.Measure.ENNRealMeasurable.iSup,
  Problib.Measure.ENNRealMeasurable.monotone_limit,
  Problib.Measure.ENNRealMeasurable.const_add,
  Problib.Measure.ENNRealMeasurable.add_const,
  Problib.Measure.ENNRealMeasurable.add,
  Problib.Measure.ENNRealMeasurable.const_mul,
  Problib.Measure.ENNRealMeasurable.mul_const,
  Problib.Measure.ENNRealMeasurable.mul,
  Problib.Measure.ENNRealMeasurable.sub,
  Problib.Measure.ENNRealMeasurable.min,
  Problib.Measure.ENNRealMeasurable.partialSum,
  Problib.Measure.ENNRealMeasurable.tsum
]

#audit_registered_claims

#audit_package [Problib.Measure.Extended] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
