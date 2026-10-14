module

public import Problib.Measure.Real.Affine
public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Kernel.Product
import Problib.Real.Grind

/-! Planar rotations preserve plane volume.

A rotation is the linear map with matrix `[[c, -s], [s, c]]`, where
`c² + s² = 1`. It keeps the squared norm of every point. It also keeps the
product Lebesgue measure on the plane, which this file proves with no change of
variables and no determinant.

The proof uses shears. A vertical shear `(x, y) ↦ (x, y + a x)` translates each
vertical section, so it keeps plane volume, because Lebesgue volume on the line
is translation invariant and the product measure integrates the sections
(`prod_apply`). Swapping the coordinates gives the horizontal shear. When
`s ≠ 0`, the rotation is a product of three shears (Paeth's decomposition),
with `a = (c - 1)/s`:

  `[[c, -s], [s, c]] = [[1, a], [0, 1]] · [[1, 0], [s, 1]] · [[1, a], [0, 1]]`.

When `s = 0`, the rotation is the identity at `c = 1`. At `c = -1` it is the
square of the quarter turn `(0, 1)`, which has a nonzero sine.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The squared Euclidean norm of a planar point. -/
@[expose] public def squaredNorm (point : Carrier × Carrier) : Carrier :=
  add (mul point.1 point.1) (mul point.2 point.2)

public theorem squaredNorm_measurable :
    MeasurableMap (Space.product borel borel) borel squaredNorm :=
  measurable_add
    (measurable_mul (Space.first_measurable borel borel) (Space.first_measurable borel borel))
    (measurable_mul (Space.second_measurable borel borel) (Space.second_measurable borel borel))

/-- The linear map with matrix `[[c, -s], [s, c]]`. It is a rotation when
`c² + s² = 1`. -/
@[expose] public def rotation (c s : Carrier) (point : Carrier × Carrier) : Carrier × Carrier :=
  (sub (mul c point.1) (mul s point.2), add (mul s point.1) (mul c point.2))

public theorem rotation_measurable (c s : Carrier) :
    MeasurableMap (Space.product borel borel) (Space.product borel borel) (rotation c s) :=
  Space.pair_measurable
    (measurable_sub
      (measurable_mul (MeasurableMap.constant _ borel c) (Space.first_measurable borel borel))
      (measurable_mul (MeasurableMap.constant _ borel s) (Space.second_measurable borel borel)))
    (measurable_add
      (measurable_mul (MeasurableMap.constant _ borel s) (Space.first_measurable borel borel))
      (measurable_mul (MeasurableMap.constant _ borel c) (Space.second_measurable borel borel)))

/-- A rotation keeps the squared norm. -/
public theorem squaredNorm_rotation {c s : Carrier} (unit : squaredNorm (c, s) = one)
    (point : Carrier × Carrier) : squaredNorm (rotation c s point) = squaredNorm point := by
  unfold squaredNorm rotation at *
  real_grind

/-- A rotation commutes with a common scaling of both coordinates. -/
public theorem rotation_scale (c s scale : Carrier) (point : Carrier × Carrier) :
    rotation c s (mul scale point.1, mul scale point.2) =
      (mul scale (rotation c s point).1, mul scale (rotation c s point).2) := by
  unfold rotation
  apply Prod.ext <;> real_grind

/-! ### Shears -/

/-- Plane volume: the product of Lebesgue volume with itself. -/
private abbrev plane : Measure (Space.product borel borel) :=
  Measure.prod volume volume volumeSFinite

private def verticalShear (shift : Carrier) (point : Carrier × Carrier) : Carrier × Carrier :=
  (point.1, add (mul shift point.1) point.2)

private def horizontalShear (shift : Carrier) (point : Carrier × Carrier) : Carrier × Carrier :=
  (add (mul shift point.2) point.1, point.2)

private theorem verticalShear_measurable (shift : Carrier) :
    MeasurableMap (Space.product borel borel) (Space.product borel borel) (verticalShear shift) :=
  Space.pair_measurable (Space.first_measurable borel borel)
    (measurable_add
      (measurable_mul (MeasurableMap.constant _ borel shift) (Space.first_measurable borel borel))
      (Space.second_measurable borel borel))

private theorem horizontalShear_measurable (shift : Carrier) :
    MeasurableMap (Space.product borel borel) (Space.product borel borel) (horizontalShear shift) :=
  Space.pair_measurable
    (measurable_add
      (measurable_mul (MeasurableMap.constant _ borel shift) (Space.second_measurable borel borel))
      (Space.first_measurable borel borel))
    (Space.second_measurable borel borel)

private theorem map_congr_function {f g : Carrier × Carrier → Carrier × Carrier}
    (fMeasurable : MeasurableMap (Space.product borel borel) (Space.product borel borel) f)
    (gMeasurable : MeasurableMap (Space.product borel borel) (Space.product borel borel) g)
    (equal : f = g) (measure : Measure (Space.product borel borel)) :
    measure.map f fMeasurable = measure.map g gMeasurable := by
  subst equal
  rfl

/-- A vertical shear translates each vertical section, so it keeps plane volume. -/
private theorem plane_verticalShear (shift : Carrier) :
    plane.map (verticalShear shift) (verticalShear_measurable shift) = plane := by
  apply Measure.ext
  intro region measurable
  rw [Measure.map_apply _ _ _ measurable,
    Measure.prod_apply _ _ _ (verticalShear_measurable shift measurable),
    Measure.prod_apply _ _ _ measurable]
  apply congrArg (lintegral volume)
  funext first
  have sectionMeasurable : borel.Measurable
      (Set.preimage (fun second : Carrier => (first, second)) region) :=
    Space.pair_measurable (MeasurableMap.constant _ borel first) (MeasurableMap.identity borel)
      measurable
  have translated := congrArg
    (fun measure : Measure borel =>
      measure (Set.preimage (fun second : Carrier => (first, second)) region))
    (map_volume_translate (mul shift first))
  rw [Measure.map_apply _ _ _ sectionMeasurable] at translated
  exact translated

private theorem plane_swap :
    plane.map (fun point : Carrier × Carrier => (point.2, point.1))
      (Space.swap_measurable borel borel) = plane :=
  Measure.prod_swap volumeSFinite volumeSFinite

/-- A horizontal shear is a vertical shear between two swaps. -/
private theorem plane_horizontalShear (shift : Carrier) :
    plane.map (horizontalShear shift) (horizontalShear_measurable shift) = plane := by
  have composed : horizontalShear shift = fun point : Carrier × Carrier =>
      ((verticalShear shift (point.2, point.1)).2, (verticalShear shift (point.2, point.1)).1) :=
    rfl
  rw [map_congr_function _
    (MeasurableMap.comp (Space.swap_measurable borel borel)
      (MeasurableMap.comp (verticalShear_measurable shift) (Space.swap_measurable borel borel)))
    composed,
    ← Measure.map_comp _ _ _ (MeasurableMap.comp (verticalShear_measurable shift)
      (Space.swap_measurable borel borel)) (Space.swap_measurable borel borel),
    ← Measure.map_comp _ _ _ (Space.swap_measurable borel borel) (verticalShear_measurable shift),
    plane_swap, plane_verticalShear, plane_swap]

/-- Paeth's decomposition: at a nonzero sine, a rotation is three shears. -/
private theorem rotation_eq_shears {c s : Carrier} (unit : squaredNorm (c, s) = one)
    (nonzero : s ≠ zero) :
    rotation c s = fun point =>
      horizontalShear (div (sub c one) s) (verticalShear s (horizontalShear (div (sub c one) s) point)) := by
  funext point
  unfold rotation horizontalShear verticalShear squaredNorm at *
  apply Prod.ext <;> real_grind

private theorem plane_rotation_of_nonzero {c s : Carrier} (unit : squaredNorm (c, s) = one)
    (nonzero : s ≠ zero) :
    plane.map (rotation c s) (rotation_measurable c s) = plane := by
  let shift := div (sub c one) s
  rw [map_congr_function _
    (MeasurableMap.comp (horizontalShear_measurable shift)
      (MeasurableMap.comp (verticalShear_measurable s) (horizontalShear_measurable shift)))
    (rotation_eq_shears unit nonzero),
    ← Measure.map_comp _ _ _ (MeasurableMap.comp (verticalShear_measurable s)
      (horizontalShear_measurable shift)) (horizontalShear_measurable shift),
    ← Measure.map_comp _ _ _ (horizontalShear_measurable shift) (verticalShear_measurable s),
    plane_horizontalShear, plane_verticalShear, plane_horizontalShear]

/-- Every rotation keeps plane volume. -/
public theorem planeVolume_rotation {c s : Carrier} (unit : squaredNorm (c, s) = one) :
    (Measure.prod volume volume volumeSFinite).map (rotation c s) (rotation_measurable c s) =
      Measure.prod volume volume volumeSFinite := by
  by_cases nonzero : s = zero
  · subst nonzero
    have square : mul (sub c one) (add c one) = zero := by
      unfold squaredNorm at unit
      real_grind
    rcases mul_eq_zero_iff.mp square with identity | negation
    · have trivial : rotation c zero = fun point => point := by
        funext point
        unfold rotation
        apply Prod.ext <;> real_grind
      rw [map_congr_function _ (MeasurableMap.identity _) trivial, Measure.map_id]
    · have quarter : squaredNorm (zero, one) = one := by
        unfold squaredNorm
        real_grind
      have half : rotation c zero = fun point => rotation zero one (rotation zero one point) := by
        funext point
        unfold rotation
        apply Prod.ext <;> real_grind
      rw [map_congr_function _ (MeasurableMap.comp (rotation_measurable zero one)
          (rotation_measurable zero one)) half,
        ← Measure.map_comp _ _ _ (rotation_measurable zero one) (rotation_measurable zero one),
        plane_rotation_of_nonzero quarter (nonzero_of_positive one_positive),
        plane_rotation_of_nonzero quarter (nonzero_of_positive one_positive)]
  · exact plane_rotation_of_nonzero unit nonzero

end

end Problib.Analysis
