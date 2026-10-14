module

public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Integral.Density.Change
import Problib.Real.Grind

set_option autoImplicit false

/-! # Change of variables for a nonzero scaling

Scaling the line by a nonzero factor `c` stretches every interval by `|c|`, so
volume pushed forward through `x ↦ c·x` is `|c|⁻¹` times volume. Weighting the
source by the Jacobian `|c|` first cancels the stretch:

  (volume.withDensity |c|).map (c · _) = volume.

This is the one-dimensional case of the equation an SMCP3 move with a Jacobian
asks of its map, `((ν ⊗ ρ).withDensity |J|).map f = ν' ⊗ ρ'`.
`lintegral_volume_scale_jacobian` is the same fact read through integrals, the
form a move's `preserves` obligation takes.

`scaleJacobian c` is `|c|` as an extended real: the positive part of `c` plus
the positive part of `-c`, one of which is zero. The positive case reuses
`map_volume_scale`, and the negative case composes it with reflection. At
`c = 0` the Jacobian is zero and the pushforward is the zero measure, so the
factor must be nonzero.
-/

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction.Dedekind

/-- `|c|`, the Jacobian of `x ↦ c·x`, as an extended real. -/
@[expose] public noncomputable def scaleJacobian (factor : Carrier) : ENNReal :=
  ENNReal.add (ENNReal.ofReal factor) (ENNReal.ofReal (neg factor))

/-- A positive factor is its own Jacobian. -/
public theorem scaleJacobian_of_positive {factor : Carrier} (positive : lt zero factor) :
    scaleJacobian factor = ENNReal.ofReal factor := by
  have negative : le (neg factor) zero := by
    have reflected := neg_le_neg_iff.mpr positive.1
    simpa only [neg_zero] using reflected
  rw [scaleJacobian, ENNReal.ofReal_eq_zero_iff.mpr negative, ENNReal.add_zero]

/-- A negative factor's Jacobian is its negation. -/
public theorem scaleJacobian_of_negative {factor : Carrier} (negative : lt factor zero) :
    scaleJacobian factor = ENNReal.ofReal (neg factor) := by
  rw [scaleJacobian, ENNReal.ofReal_eq_zero_iff.mpr negative.1, ENNReal.zero_add]

/-- A nonnegative factor is its own Jacobian. -/
public theorem scaleJacobian_of_nonnegative {factor : Carrier} (nonnegative : le zero factor) :
    scaleJacobian factor = ENNReal.ofReal factor := by
  have reflected : le (neg factor) zero := by real_grind
  rw [scaleJacobian, ENNReal.ofReal_eq_zero_iff.mpr reflected, ENNReal.add_zero]

/-- A nonpositive factor's Jacobian is its negation. -/
public theorem scaleJacobian_of_nonpositive {factor : Carrier} (nonpositive : le factor zero) :
    scaleJacobian factor = ENNReal.ofReal (neg factor) := by
  rw [scaleJacobian, ENNReal.ofReal_eq_zero_iff.mpr nonpositive, ENNReal.zero_add]

/-- The Jacobian of a product of scalings is the product of their Jacobians. -/
public theorem scaleJacobian_mul (left right : Carrier) :
    scaleJacobian (mul left right) =
      ENNReal.mul (scaleJacobian left) (scaleJacobian right) := by
  rcases le_total zero left with leftUp | leftDown <;>
    rcases le_total zero right with rightUp | rightDown
  · rw [scaleJacobian_of_nonnegative (mul_nonnegative leftUp rightUp),
      scaleJacobian_of_nonnegative leftUp, scaleJacobian_of_nonnegative rightUp,
      ofReal_mul leftUp rightUp]
  · have flipped : le zero (neg right) := by real_grind
    have product := mul_nonnegative leftUp flipped
    rw [scaleJacobian_of_nonpositive (by real_grind : le (mul left right) zero),
      scaleJacobian_of_nonnegative leftUp, scaleJacobian_of_nonpositive rightDown,
      ← ofReal_mul leftUp flipped]
    congr 1
    real_grind
  · have flipped : le zero (neg left) := by real_grind
    have product := mul_nonnegative flipped rightUp
    rw [scaleJacobian_of_nonpositive (by real_grind : le (mul left right) zero),
      scaleJacobian_of_nonpositive leftDown, scaleJacobian_of_nonnegative rightUp,
      ← ofReal_mul flipped rightUp]
    congr 1
    real_grind
  · have leftFlipped : le zero (neg left) := by real_grind
    have rightFlipped : le zero (neg right) := by real_grind
    have product := mul_nonnegative leftFlipped rightFlipped
    rw [scaleJacobian_of_nonnegative (by real_grind : le zero (mul left right)),
      scaleJacobian_of_nonpositive leftDown, scaleJacobian_of_nonpositive rightDown,
      ← ofReal_mul leftFlipped rightFlipped]
    congr 1
    real_grind

public theorem scaleJacobian_one : scaleJacobian one = ENNReal.one := by
  rw [scaleJacobian_of_nonnegative one_positive.1, ENNReal.ofReal_one]

/-- A Jacobian is finite. -/
public theorem scaleJacobian_finite (factor : Carrier) : ENNReal.Finite (scaleJacobian factor) := by
  rcases le_total zero factor with up | down
  · rw [scaleJacobian_of_nonnegative up]
    exact ENNReal.ofReal_finite _
  · rw [scaleJacobian_of_nonpositive down]
    exact ENNReal.ofReal_finite _

/-- Multiplication by any constant is Borel measurable. -/
public theorem scale_measurable_any (factor : Carrier) :
    MeasurableMap borel borel (mul factor) :=
  measurable_mul (MeasurableMap.constant borel borel factor) (MeasurableMap.identity borel)

/-- Volume weighted by the Jacobian `|c|` and pushed through `x ↦ c·x` is
volume, for every nonzero `c`. -/
public theorem map_withDensity_volume_scale (factor : Carrier) (nonzero : factor ≠ zero) :
    (volume.withDensity (fun _ => scaleJacobian factor)).map (mul factor)
      (scale_measurable_any factor) = volume := by
  rw [volume.withDensity_const, Measure.map_smul]
  rcases negative_or_positive_of_nonzero nonzero with negative | positive
  · have reflected : lt zero (neg factor) := by
      have flipped := neg_lt_neg_iff.mpr negative
      simpa only [neg_zero] using flipped
    have through : volume.map (mul factor) (scale_measurable_any factor) =
        (volume.map (mul (neg factor)) (scale_measurable (neg factor) reflected.1)).map neg
          neg_measurable := by
      rw [Measure.map_comp]
      congr 1
      funext value
      rw [neg_mul, neg_neg]
    rw [through, map_volume_scale (neg factor) reflected, Measure.map_smul, map_volume_neg,
      Measure.smul_smul, scaleJacobian_of_negative negative,
      ofReal_mul_ofReal_inverse reflected, Measure.one_smul]
  · rw [map_volume_scale factor positive, Measure.smul_smul, scaleJacobian_of_positive positive,
      ofReal_mul_ofReal_inverse positive, Measure.one_smul]

/-- The change of variables as integrals: the integrand read at `c·x` and
weighted by `|c|` integrates to the integrand's volume integral. -/
public theorem lintegral_volume_scale_jacobian (factor : Carrier) (nonzero : factor ≠ zero)
    {integrand : Carrier → ENNReal} (measurable : ENNRealMeasurable borel integrand) :
    lintegral volume (fun value => ENNReal.mul (scaleJacobian factor) (integrand (mul factor value))) =
      lintegral volume integrand := by
  rw [← lintegral_withDensity volume (ENNRealMeasurable.constant _ _)
      (measurable.comp (scale_measurable_any factor)),
    ← lintegral_map _ _ (scale_measurable_any factor) measurable,
    map_withDensity_volume_scale factor nonzero]

end Problib.Measure.Real
