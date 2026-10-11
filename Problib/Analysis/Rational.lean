module

public import Init.Data.Rat.Lemmas

/-! Scalar limits for the exact rational interpretation of finite programs.
The quantifiers range over rational displacements and tolerances. Real-carrier
analysis requires its own interpretation and transport evidence.
-/

set_option autoImplicit false

namespace Problib.Analysis.Rational

/-- A two-sided epsilon-delta derivative on the rational scalar carrier. -/
public def HasDerivative (function : Rat → Rat) (point derivative : Rat) : Prop :=
  ∀ epsilon : Rat, 0 < epsilon → ∃ radius : Rat, 0 < radius ∧
    ∀ displacement : Rat, displacement ≠ 0 → displacement.abs < radius →
      (((function (point + displacement) - function point) / displacement) - derivative).abs < epsilon

public theorem abs_le {value bound : Rat} :
    value.abs ≤ bound ↔ -bound ≤ value ∧ value ≤ bound := by
  simp only [Rat.abs]
  split <;> grind

public theorem abs_lt {value bound : Rat} :
    value.abs < bound ↔ -bound < value ∧ value < bound := by
  simp only [Rat.abs]
  split <;> grind

public theorem abs_add_le (left right : Rat) :
    (left + right).abs ≤ left.abs + right.abs := by
  have first := abs_le.mp (show left.abs ≤ left.abs from Rat.le_refl)
  have second := abs_le.mp (show right.abs ≤ right.abs from Rat.le_refl)
  apply abs_le.mpr
  grind

public theorem abs_mul (left right : Rat) : (left * right).abs = left.abs * right.abs := by
  by_cases first : 0 ≤ left <;> by_cases second : 0 ≤ right
  · rw [Rat.abs_of_nonneg first, Rat.abs_of_nonneg second,
      Rat.abs_of_nonneg (Rat.mul_nonneg first second)]
  · have secondNeg : 0 ≤ -right := by grind
    have product := Rat.mul_nonneg first secondNeg
    rw [Rat.abs_of_nonneg first, Rat.abs_of_nonpos (by grind : right ≤ 0),
      Rat.abs_of_nonpos (by grind : left * right ≤ 0)]
    grind
  · have firstNeg : 0 ≤ -left := by grind
    have product := Rat.mul_nonneg firstNeg second
    rw [Rat.abs_of_nonpos (by grind : left ≤ 0), Rat.abs_of_nonneg second,
      Rat.abs_of_nonpos (by grind : left * right ≤ 0)]
    grind
  · have firstNeg : 0 ≤ -left := by grind
    have secondNeg : 0 ≤ -right := by grind
    have product := Rat.mul_nonneg firstNeg secondNeg
    rw [Rat.abs_of_nonpos (by grind : left ≤ 0), Rat.abs_of_nonpos (by grind : right ≤ 0),
      Rat.abs_of_nonneg (by grind : 0 ≤ left * right)]
    grind

public theorem abs_inv (value : Rat) : value⁻¹.abs = value.abs⁻¹ := by
  by_cases zero : value = 0
  · subst value; simp
  · apply Eq.symm
    apply Rat.inv_eq_of_mul_eq_one
    rw [← abs_mul, Rat.mul_inv_cancel value zero]
    decide +kernel

public theorem abs_div (left right : Rat) : (left / right).abs = left.abs / right.abs := by
  simp only [Rat.div_def, abs_mul, abs_inv]

public theorem small_positive {left right : Rat} (first : 0 < left) (second : 0 < right) :
    ∃ value : Rat, 0 < value ∧ value ≤ left ∧ value ≤ right := by
  by_cases smaller : left ≤ right
  · exact ⟨left, first, Rat.le_refl, smaller⟩
  · exact ⟨right, second, by grind, Rat.le_refl⟩

/-- A linear error bound on difference quotients entails the limit definition.
The bound is local and applies to every nonzero sufficiently small displacement. -/
public theorem derivative_of_secant_bound (function : Rat → Rat) (point derivative radius constant : Rat)
    (radiusPositive : 0 < radius) (constantNonnegative : 0 ≤ constant)
    (bound : ∀ displacement : Rat, displacement ≠ 0 → displacement.abs < radius →
      (((function (point + displacement) - function point) / displacement) - derivative).abs ≤
        constant * displacement.abs) : HasDerivative function point derivative := by
  intro epsilon positive
  have divisorPositive : 0 < constant + 1 := by grind
  have tolerancePositive : 0 < epsilon / (constant + 1) := by
    rw [Rat.div_def]
    exact Rat.mul_pos positive (Rat.inv_pos.mpr divisorPositive)
  rcases small_positive radiusPositive tolerancePositive with ⟨delta, deltaPositive, radiusBound, errorBound⟩
  refine ⟨delta, deltaPositive, ?_⟩
  intro displacement nonzero small
  have within : displacement.abs < radius := by grind
  have scaled := (Rat.lt_div_iff divisorPositive).mp (by grind : displacement.abs < epsilon / (constant + 1))
  have nonnegative := Rat.abs_nonneg (x := displacement)
  have smaller : constant * displacement.abs ≤ displacement.abs * (constant + 1) := by grind
  have finalBound := bound displacement nonzero within
  grind

/-- Exact error identity for an affine numerator divided by an affine normalizer. -/
public theorem affine_quotient_secant (a b c d point displacement : Rat)
    (nonzero : c * point + d ≠ 0) (nearby : c * (point + displacement) + d ≠ 0)
    (step : displacement ≠ 0) :
    ((((a * (point + displacement) + b) / (c * (point + displacement) + d)) -
      ((a * point + b) / (c * point + d))) / displacement -
        (a * d - b * c) / ((c * point + d) * (c * point + d))) =
      -(a * d - b * c) * c * displacement /
        ((c * point + d) * (c * point + d) * (c * (point + displacement) + d)) := by
  have first := Rat.mul_inv_cancel (c * point + d) nonzero
  have second := Rat.mul_inv_cancel (c * (point + displacement) + d) nearby
  have third := Rat.mul_inv_cancel displacement step
  simp only [Rat.div_def, Rat.inv_mul_rev]
  grind

/-- A positive affine denominator stays positive on an explicit neighborhood. -/
public theorem affine_denominator_near (value slope displacement : Rat)
    (small : displacement.abs < value / (2 * (slope.abs + 1))) :
    value / 2 < value + slope * displacement := by
  have slopeNonnegative := Rat.abs_nonneg (x := slope)
  have stepNonnegative := Rat.abs_nonneg (x := displacement)
  have divisorPositive : 0 < 2 * (slope.abs + 1) := by grind
  have scaled := (Rat.lt_div_iff divisorPositive).mp small
  have errorBound : (slope * displacement).abs < value / 2 := by
    rw [abs_mul]
    apply (Rat.lt_div_iff (by decide +kernel : (0 : Rat) < 2)).mpr
    grind
  have error := abs_lt.mp errorBound
  grind

/-- The reciprocal bound used by normalized finite expectations. -/
public theorem inverse_le_two_div {value nearby : Rat} (positive : 0 < value)
    (lower : value / 2 < nearby) : nearby⁻¹ ≤ 2 / value := by
  have nearbyPositive : 0 < nearby := by grind
  have first := Rat.mul_inv_cancel value (Rat.ne_of_gt positive)
  have rearranged : 2 * value⁻¹ * nearby * value = 2 * nearby := by grind
  apply Rat.le_of_mul_le_mul_right (hc := nearbyPositive)
  apply Rat.le_of_mul_le_mul_right (hc := positive)
  simp only [Rat.div_def]
  rw [Rat.inv_mul_cancel nearby (Rat.ne_of_gt nearbyPositive), Rat.one_mul, rearranged]
  have scaled := (Rat.div_lt_iff (by decide +kernel : (0 : Rat) < 2)).mp lower
  grind

/-- Differentiating a normalized affine finite sum obeys the quotient rule.
A positive normalizer supplies a neighborhood, not just a pointwise quotient. -/
public theorem affine_quotient_derivative (a b c d point : Rat)
    (positive : 0 < c * point + d) :
    HasDerivative (fun parameter => (a * parameter + b) / (c * parameter + d)) point
      ((a * d - b * c) / ((c * point + d) * (c * point + d))) := by
  let value := c * point + d
  let numerator := (a * d - b * c).abs * c.abs
  let radius := value / (2 * (c.abs + 1))
  let constant := 2 * numerator / (value * value * value)
  have valuePositive : 0 < value := positive
  have squarePositive := Rat.mul_pos valuePositive valuePositive
  have cubePositive := Rat.mul_pos squarePositive valuePositive
  have numeratorNonnegative : 0 ≤ numerator := Rat.mul_nonneg Rat.abs_nonneg Rat.abs_nonneg
  have radiusPositive : 0 < radius := by
    have slopeNonnegative := Rat.abs_nonneg (x := c)
    have divisorPositive : 0 < 2 * (c.abs + 1) := by grind
    exact Rat.mul_pos valuePositive (Rat.inv_pos.mpr divisorPositive)
  have constantNonnegative : 0 ≤ constant := by
    exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) numeratorNonnegative)
      (Rat.le_of_lt (Rat.inv_pos.mpr cubePositive))
  apply derivative_of_secant_bound _ point _ radius constant radiusPositive constantNonnegative
  intro displacement nonzero small
  have lower := affine_denominator_near value c displacement small
  have nearbyPositive : 0 < value + c * displacement := by grind
  have nearby : c * (point + displacement) + d ≠ 0 := by
    have equal : c * (point + displacement) + d = value + c * displacement := by dsimp [value]; grind
    rw [equal]
    exact Rat.ne_of_gt nearbyPositive
  rw [affine_quotient_secant a b c d point displacement (Rat.ne_of_gt positive) nearby nonzero]
  have reciprocal := inverse_le_two_div valuePositive lower
  have factorNonnegative : 0 ≤ numerator / (value * value) * displacement.abs :=
    Rat.mul_nonneg (Rat.mul_nonneg numeratorNonnegative
      (Rat.le_of_lt (Rat.inv_pos.mpr squarePositive))) Rat.abs_nonneg
  have estimate := Rat.mul_le_mul_of_nonneg_left reciprocal factorNonnegative
  have denominatorPositive : 0 < (c * point + d) * (c * point + d) *
      (c * (point + displacement) + d) := by
    apply Rat.mul_pos squarePositive
    have equal : c * (point + displacement) + d = value + c * displacement := by dsimp [value]; grind
    rw [equal]
    exact nearbyPositive
  rw [abs_div, Rat.abs_of_nonneg (Rat.le_of_lt denominatorPositive)]
  simp only [abs_mul, Rat.abs_neg]
  simp only [Rat.div_def, Rat.inv_mul_rev] at estimate ⊢
  dsimp [constant, numerator, value] at estimate ⊢
  simp only [Rat.div_def, Rat.inv_mul_rev]
  grind

/-- Limits of difference quotients determine a unique scalar derivative. -/
public theorem HasDerivative.unique {function : Rat → Rat} {point first second : Rat}
    (firstLaw : HasDerivative function point first) (secondLaw : HasDerivative function point second) :
    first = second := by
  apply Classical.byContradiction
  intro different
  have gapPositive : 0 < (first - second).abs := Rat.abs_pos_iff.mpr (by grind)
  have epsilonPositive : 0 < (first - second).abs / 3 := by
    rw [Rat.div_def]
    exact Rat.mul_pos gapPositive (by decide +kernel)
  rcases firstLaw _ epsilonPositive with ⟨firstRadius, firstPositive, firstBound⟩
  rcases secondLaw _ epsilonPositive with ⟨secondRadius, secondPositive, secondBound⟩
  rcases small_positive firstPositive secondPositive with ⟨radius, positive, firstNear, secondNear⟩
  let displacement := radius / 2
  have displacementPositive : 0 < displacement := by dsimp [displacement]; grind
  have small : displacement.abs < radius := by
    rw [Rat.abs_of_nonneg (Rat.le_of_lt displacementPositive)]
    dsimp [displacement]
    grind
  have firstError := firstBound displacement (Rat.ne_of_gt displacementPositive) (by grind)
  have secondError := secondBound displacement (Rat.ne_of_gt displacementPositive) (by grind)
  let quotient := (function (point + displacement) - function point) / displacement
  have opposite : (first - quotient).abs = (quotient - first).abs := Rat.abs_sub_comm
  have triangle := abs_add_le (first - quotient) (quotient - second)
  have sum : (first - quotient) + (quotient - second) = first - second := by grind
  rw [sum, opposite] at triangle
  change (quotient - first).abs < _ at firstError
  change (quotient - second).abs < _ at secondError
  grind

end Problib.Analysis.Rational
