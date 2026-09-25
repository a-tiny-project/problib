module

public import Problib.Measure.Extended.Limit
public import Problib.Real.Series.Ratio

set_option autoImplicit false

/-!
# Measurability of extended nonnegative real density ratios

Proves that the pointwise density ratio `ENNReal.densityRatio` of two measurable
extended nonnegative real functions is measurable.
-/

namespace Problib.Measure.ENNRealMeasurable

open Problib.Real

universe u

/-- Pointwise density ratio of two measurable extended nonnegative real functions is measurable. -/
public theorem densityRatio {α : Type u} {space : Space α} {target reference : α → ENNReal}
    (targetMeasurable : ENNRealMeasurable space target)
    (referenceMeasurable : ENNRealMeasurable space reference) :
    ENNRealMeasurable space (fun value => ENNReal.densityRatio (target value) (reference value)) := by
  classical
  have constant := ENNRealMeasurable.constant space
  have referenceZero := referenceMeasurable.eq_set (constant ENNReal.zero)
  have referenceTop := referenceMeasurable.eq_set (constant ENNReal.top)
  have targetZero := targetMeasurable.eq_set (constant ENNReal.zero)
  have cuts := ENNRealMeasurable.iSup (fun index =>
    ENNRealMeasurable.piecewise
      ((referenceMeasurable.mul (constant (ENNReal.rationalBasis index))).le_set targetMeasurable)
      (constant (ENNReal.rationalBasis index)) (constant ENNReal.zero))
  have ratio := ENNRealMeasurable.piecewise referenceZero (constant ENNReal.zero)
    (ENNRealMeasurable.piecewise referenceTop
      (ENNRealMeasurable.piecewise targetZero (constant ENNReal.zero) (constant ENNReal.one)) cuts)
  unfold ennrealPiecewise at ratio
  exact ratio

end Problib.Measure.ENNRealMeasurable
