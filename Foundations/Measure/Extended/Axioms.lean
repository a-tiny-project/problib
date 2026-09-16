import Foundations.Measure.Extended
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.ENNRealMeasurable.densityRatio,
  Foundations.Measure.Real.unitRationalBasis,
  Foundations.Measure.Real.existsUnitRationalBasisBetween,
  Foundations.Measure.Real.toRealMeasurable,
  Foundations.Measure.Real.unitClamp,
  Foundations.Measure.Real.ofReal_unitClamp,
  Foundations.Measure.Real.ofReal_unitClamp_of_le,
  Foundations.Measure.Real.unitClamp_ofReal,
  Foundations.Measure.Real.unitClamp_top,
  Foundations.Measure.Real.unitClamp_mono,
  Foundations.Measure.Real.unitClampMeasurable,
  Foundations.Measure.ENNRealMeasurable.iInf,
  Foundations.Measure.Real.ofRealMeasurable,
  Foundations.Measure.ENNRealMeasurable.max,
  Foundations.Measure.ENNRealMeasurable.prefixMax,
  Foundations.Measure.ennrealBorel_generator,
  Foundations.Measure.ennrealBorel_minimal,
  Foundations.Measure.ENNRealMeasurable.measurableMap,
  Foundations.Measure.ENNRealMeasurable.ofMeasurableMap,
  Foundations.Measure.ENNRealMeasurable.measurableMap_iff,
  Foundations.Measure.ENNRealMeasurable.ioi,
  Foundations.Measure.ENNRealMeasurable.constant,
  Foundations.Measure.ENNRealMeasurable.identity,
  Foundations.Measure.ENNRealMeasurable.comp,
  Foundations.Measure.ENNRealMeasurable.piecewise,
  Foundations.Measure.ENNRealMeasurable.indicator,
  Foundations.Measure.ENNRealMeasurable.iic,
  Foundations.Measure.ENNRealMeasurable.iio,
  Foundations.Measure.ENNRealMeasurable.ici,
  Foundations.Measure.ENNRealMeasurable.singleton,
  Foundations.Measure.ENNRealMeasurable.lt_set,
  Foundations.Measure.ENNRealMeasurable.le_set,
  Foundations.Measure.ENNRealMeasurable.eq_set,
  Foundations.Measure.ENNRealMeasurable.approximation,
  Foundations.Measure.ENNRealMeasurable.iSup,
  Foundations.Measure.ENNRealMeasurable.monotoneLimit,
  Foundations.Measure.ENNRealMeasurable.const_add,
  Foundations.Measure.ENNRealMeasurable.add_const,
  Foundations.Measure.ENNRealMeasurable.add,
  Foundations.Measure.ENNRealMeasurable.const_mul,
  Foundations.Measure.ENNRealMeasurable.mul_const,
  Foundations.Measure.ENNRealMeasurable.mul,
  Foundations.Measure.ENNRealMeasurable.sub,
  Foundations.Measure.ENNRealMeasurable.min,
  Foundations.Measure.ENNRealMeasurable.partialSum,
  Foundations.Measure.ENNRealMeasurable.tsum
]

#audit_registered_claims

#audit_package [Foundations.Measure.Extended] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
