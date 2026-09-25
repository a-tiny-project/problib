module

public import Problib.Real.Extended.Order

set_option autoImplicit false

namespace Problib.Real.ENNReal

/-- Minimum of two extended nonnegative real numbers. -/
@[expose] public noncomputable def min (left right : ENNReal) : ENNReal := by
  classical
  exact if included : le left right then left else right

public theorem min_eq_left {left right : ENNReal} (included : le left right) :
    min left right = left := by
  classical
  unfold min
  simp only [dif_pos included]

public theorem min_eq_right {left right : ENNReal} (included : le right left) :
    min left right = right := by
  classical
  by_cases reverse : le left right
  · rw [min_eq_left reverse, le_antisymm reverse included]
  · unfold min
    simp only [dif_neg reverse]

public theorem min_le_left (left right : ENNReal) : le (min left right) left := by
  rcases le_total left right with included | included
  · rw [min_eq_left included]
    exact le_refl left
  · rw [min_eq_right included]
    exact included

public theorem min_le_right (left right : ENNReal) : le (min left right) right := by
  rw [show min left right = min right left by
    rcases le_total left right with included | included
    · rw [min_eq_left included, min_eq_right included]
    · rw [min_eq_right included, min_eq_left included]]
  exact min_le_left right left

public theorem le_min {left right lower : ENNReal}
    (leftIncluded : le lower left) (rightIncluded : le lower right) :
    le lower (min left right) := by
  rcases le_total left right with included | included
  · rw [min_eq_left included]
    exact leftIncluded
  · rw [min_eq_right included]
    exact rightIncluded

/-- Maximum of two extended nonnegative real numbers. -/
@[expose] public noncomputable def max (left right : ENNReal) : ENNReal := by
  classical
  exact if included : le left right then right else left

public theorem max_eq_right {left right : ENNReal} (included : le left right) :
    max left right = right := by
  classical
  unfold max
  simp only [dif_pos included]

public theorem max_eq_left {left right : ENNReal} (included : le right left) :
    max left right = left := by
  classical
  by_cases reverse : le left right
  · rw [max_eq_right reverse, le_antisymm included reverse]
  · unfold max
    simp only [dif_neg reverse]

public theorem le_max_left (left right : ENNReal) : le left (max left right) := by
  rcases le_total left right with included | included
  · rw [max_eq_right included]
    exact included
  · rw [max_eq_left included]
    exact le_refl left

public theorem le_max_right (left right : ENNReal) : le right (max left right) := by
  rcases le_total left right with included | included
  · rw [max_eq_right included]
    exact le_refl right
  · rw [max_eq_left included]
    exact included

public theorem max_le {left right upper : ENNReal}
    (leftIncluded : le left upper) (rightIncluded : le right upper) :
    le (max left right) upper := by
  rcases le_total left right with included | included
  · rw [max_eq_right included]
    exact rightIncluded
  · rw [max_eq_left included]
    exact leftIncluded

end Problib.Real.ENNReal
