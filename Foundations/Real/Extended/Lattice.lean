module

public import Foundations.Real.Extended.Order

set_option autoImplicit false

namespace Foundations.Real.ENNReal

/-- Minimum of two extended nonnegative real numbers. -/
@[expose] public noncomputable def min (left right : ENNReal) : ENNReal := by
  classical
  exact if included : le left right then left else right

public theorem minEqLeft {left right : ENNReal} (included : le left right) :
    min left right = left := by
  classical
  unfold min
  simp only [dif_pos included]

public theorem minEqRight {left right : ENNReal} (included : le right left) :
    min left right = right := by
  classical
  by_cases reverse : le left right
  · rw [minEqLeft reverse, leAntisymm reverse included]
  · unfold min
    simp only [dif_neg reverse]

public theorem minLeLeft (left right : ENNReal) : le (min left right) left := by
  rcases leTotal left right with included | included
  · rw [minEqLeft included]
    exact leRefl left
  · rw [minEqRight included]
    exact included

public theorem minLeRight (left right : ENNReal) : le (min left right) right := by
  rw [show min left right = min right left by
    rcases leTotal left right with included | included
    · rw [minEqLeft included, minEqRight included]
    · rw [minEqRight included, minEqLeft included]]
  exact minLeLeft right left

public theorem leMin {left right lower : ENNReal}
    (leftIncluded : le lower left) (rightIncluded : le lower right) :
    le lower (min left right) := by
  rcases leTotal left right with included | included
  · rw [minEqLeft included]
    exact leftIncluded
  · rw [minEqRight included]
    exact rightIncluded

/-- Maximum of two extended nonnegative real numbers. -/
@[expose] public noncomputable def max (left right : ENNReal) : ENNReal := by
  classical
  exact if included : le left right then right else left

public theorem maxEqRight {left right : ENNReal} (included : le left right) :
    max left right = right := by
  classical
  unfold max
  simp only [dif_pos included]

public theorem maxEqLeft {left right : ENNReal} (included : le right left) :
    max left right = left := by
  classical
  by_cases reverse : le left right
  · rw [maxEqRight reverse, leAntisymm included reverse]
  · unfold max
    simp only [dif_neg reverse]

public theorem leMaxLeft (left right : ENNReal) : le left (max left right) := by
  rcases leTotal left right with included | included
  · rw [maxEqRight included]
    exact included
  · rw [maxEqLeft included]
    exact leRefl left

public theorem leMaxRight (left right : ENNReal) : le right (max left right) := by
  rcases leTotal left right with included | included
  · rw [maxEqRight included]
    exact leRefl right
  · rw [maxEqLeft included]
    exact included

public theorem maxLe {left right upper : ENNReal}
    (leftIncluded : le left upper) (rightIncluded : le right upper) :
    le (max left right) upper := by
  rcases leTotal left right with included | included
  · rw [maxEqRight included]
    exact rightIncluded
  · rw [maxEqLeft included]
    exact leftIncluded

end Foundations.Real.ENNReal
