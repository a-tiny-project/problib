module

public import Problib.Analysis.Real.Matrix.Determinant
public import Problib.Measure.Real.Invariant
public import Problib.Measure.Real.Scale
public import Problib.Measure.Real.Simplex
import Problib.Real.Grind

/-! # Volume change under an upper triangular matrix

An upper triangular matrix `R` with nonzero determinant multiplies volume by
`|det R|`: for every measurable `E`, `λ(R E) = |det R| · λ(E)`
(`volumePi_image_upperTriangular`). Read as a pushforward, volume weighted by
the Jacobian `|det R|` and pushed through `R` is volume
(`map_withDensity_volumePi_upperTriangular`), the form `Scale.lean` gives on
the line.

The proof adds one coordinate at a time, in the order `volumePi_succ` prepends
them. Write a point as `(x₀, t)` with `t` the remaining coordinates. Its image
is `(r x₀ + ℓ t, T t)`, where `r = R 0 0`, `ℓ t` is the rest of the first
row applied to `t`, and `T = tail R`. That map is three steps on
`volume ⊗ volumePi n`, each with a known effect on volume:

- scale the first coordinate by `r`, which multiplies volume by `|r|⁻¹`;
- shear it by `ℓ t`, a translation within each fiber, which keeps volume;
- apply `T` to the rest, which multiplies volume by `|det T|⁻¹` by induction.

Since `det R = r · det T`, the factors multiply to `|det R|⁻¹`.
-/

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.Matrix (UpperTriangular)

public section

/-- A finite sum of measurable real functions is measurable. -/
theorem sum_measurable {α : Type} {source : Space α} (dimension : Nat)
    {terms : Fin dimension → α → Carrier} (measurable : ∀ index, MeasurableMap source borel (terms index)) :
    MeasurableMap source borel (fun point => Matrix.sum dimension fun index => terms index point) :=
  have vector : MeasurableMap source (Space.pi (fun _ : Fin dimension => borel))
      (fun point index => terms index point) :=
    Space.pi_measurable measurable
  fun target => vector (finSum_measurable dimension target)

theorem apply_measurable {rows columns : Nat} (matrix : Matrix.carrier rows columns) :
    MeasurableMap (Space.pi (fun _ : Fin columns => borel)) (Space.pi (fun _ : Fin rows => borel))
      (Matrix.apply matrix) :=
  Space.pi_measurable fun row =>
    sum_measurable columns (terms := fun index (point : Fin columns → Carrier) =>
      mul (matrix row index) (point index)) fun index => fun target =>
      Space.coordinate_measurable (fun _ : Fin columns => borel) index
        (scale_measurable_any (matrix row index) target)

theorem solve_measurable : {dimension : Nat} → (matrix : Matrix.carrier dimension dimension) →
    MeasurableMap (Space.pi (fun _ : Fin dimension => borel))
      (Space.pi (fun _ : Fin dimension => borel)) (Matrix.solve matrix)
  | 0, _ => MeasurableMap.identity _
  | dimension + 1, matrix =>
      have tailMeasurable : MeasurableMap (Space.pi (fun _ : Fin (dimension + 1) => borel))
          (Space.pi (fun _ : Fin dimension => borel)) (fun target index => target index.succ) :=
        Space.pi_measurable fun index =>
          Space.coordinate_measurable (fun _ : Fin (dimension + 1) => borel) index.succ
      have restMeasurable : MeasurableMap (Space.pi (fun _ : Fin (dimension + 1) => borel))
          (Space.pi (fun _ : Fin dimension => borel))
          (fun target => Matrix.solve (Matrix.tail matrix) fun row => target row.succ) :=
        fun target => tailMeasurable (solve_measurable (Matrix.tail matrix) target)
      have entryMeasurable (index : Fin dimension) :
          MeasurableMap (Space.pi (fun _ : Fin (dimension + 1) => borel)) borel
            (fun target => Matrix.solve (Matrix.tail matrix) (fun row => target row.succ) index) :=
        fun target =>
          restMeasurable (Space.coordinate_measurable (fun _ : Fin dimension => borel) index target)
      have leadingMeasurable : MeasurableMap (Space.pi (fun _ : Fin (dimension + 1) => borel)) borel
          (fun target => div (sub (target 0)
            (Matrix.sum dimension fun column => mul (matrix 0 column.succ)
              (Matrix.solve (Matrix.tail matrix) (fun row => target row.succ) column)))
            (matrix 0 0)) :=
        measurable_div
          (measurable_sub (Space.coordinate_measurable (fun _ : Fin (dimension + 1) => borel) 0)
            (sum_measurable dimension (terms := fun column (target : Fin (dimension + 1) → Carrier) =>
              mul (matrix 0 column.succ)
                (Matrix.solve (Matrix.tail matrix) (fun row => target row.succ) column))
              fun column => fun target =>
                entryMeasurable column (scale_measurable_any (matrix 0 column.succ) target)))
          (MeasurableMap.constant _ borel (matrix 0 0))
      Space.pi_measurable fun index =>
        Fin.cases (motive := fun index => MeasurableMap (Space.pi (fun _ : Fin (dimension + 1) => borel))
            borel (fun target => Matrix.solve matrix target index))
          leadingMeasurable entryMeasurable index

/-- Scaling the line by a nonzero factor divides volume by its Jacobian. -/
theorem smul_map_volume_scale (factor : Carrier) (nonzero : factor ≠ zero) :
    Measure.smul (scaleJacobian factor) (volume.map (mul factor) (scale_measurable_any factor)) =
      volume := by
  have weighted := map_withDensity_volume_scale factor nonzero
  rwa [volume.withDensity_const, Measure.map_smul] at weighted

/-- Volume weighted by `|det R|` and pushed through an upper triangular `R` is
volume. The statement scales the pushforward, `|det R| · R_*λ = λ`. -/
theorem smul_map_volumePi_upperTriangular : {dimension : Nat} →
    {matrix : Matrix.carrier dimension dimension} → UpperTriangular matrix →
    Matrix.det matrix ≠ zero →
    Measure.smul (scaleJacobian (Matrix.det matrix))
        ((volumePi dimension).map (Matrix.apply matrix) (apply_measurable matrix)) =
      volumePi dimension
  | 0, matrix, _, _ => by
      have identity : Matrix.apply matrix = fun point => point :=
        funext fun _ => funext fun index => index.elim0
      change Measure.smul (scaleJacobian one) _ = _
      rw [scaleJacobian_one, Measure.one_smul,
        Measure.map_congr_function _ _ (MeasurableMap.identity _) identity, Measure.map_id]
  | dimension + 1, matrix, upper, nonzero => by
      let leading := matrix 0 0
      let rest := Matrix.tail matrix
      let shift : (Fin dimension → Carrier) → Carrier := fun point =>
        Matrix.sum dimension fun index => mul (matrix 0 index.succ) (point index)
      have diagonal := (Matrix.det_ne_zero_iff upper).mp nonzero
      have restNonzero : Matrix.det rest ≠ zero :=
        (Matrix.det_ne_zero_iff upper.tail).mpr fun index => diagonal index.succ
      have shiftMeasurable : MeasurableMap (Space.pi (fun _ : Fin dimension => borel)) borel shift :=
        sum_measurable dimension fun index =>
          MeasurableMap.comp (scale_measurable_any (matrix 0 index.succ))
            (Space.coordinate_measurable (fun _ : Fin dimension => borel) index)
      let pairSpace := Space.product borel (Space.pi (fun _ : Fin dimension => borel))
      have stretchMeasurable : MeasurableMap pairSpace pairSpace
          (fun pair => (mul leading pair.1, (fun point => point) pair.2)) :=
        Space.product_map (scale_measurable_any leading) (MeasurableMap.identity _)
      have shearMeasurable : MeasurableMap pairSpace pairSpace
          (fun pair => (add (shift pair.2) pair.1, pair.2)) :=
        Space.pair_measurable
          (measurable_add (MeasurableMap.comp shiftMeasurable (Space.second_measurable _ _))
            (Space.first_measurable _ _))
          (Space.second_measurable _ _)
      have lowerMeasurable : MeasurableMap pairSpace pairSpace
          (fun pair => ((fun value => value) pair.1, Matrix.apply rest pair.2)) :=
        Space.product_map (MeasurableMap.identity _) (apply_measurable rest)
      -- The image of `(x₀, t)` is `(r x₀ + ℓ t, T t)`.
      have commute : (fun pair => Matrix.apply matrix (finCons dimension pair)) =
          (fun pair => finCons dimension
            (add (shift pair.2) (mul leading pair.1), Matrix.apply rest pair.2)) := by
        funext pair index
        refine Fin.cases ?_ (fun index => ?_) index
        · change add (mul leading pair.1) (shift pair.2) = add (shift pair.2) (mul leading pair.1)
          exact add_comm _ _
        · exact Matrix.apply_succ_row upper (finCons dimension pair) index
      -- Scaling the first coordinate.
      have stretched : Measure.smul (scaleJacobian leading)
          ((Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map _ stretchMeasurable) =
          Measure.prod volume (volumePi dimension) (volumePiSFinite dimension) := by
        change Measure.smul _ (Measure.map (Measure.prod _ _ _) _ _) = _
        rw [Measure.prod_map _ _ _ _ _ (scale_measurable_any leading) (MeasurableMap.identity _),
          Measure.prod_congr_right _ _ (volumePiSFinite dimension) (Measure.map_id _),
          ← Measure.prod_smul_left, smul_map_volume_scale leading (diagonal 0)]
      -- Shearing it by `ℓ t`.
      have sheared : (Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map _ shearMeasurable =
          Measure.prod volume (volumePi dimension) (volumePiSFinite dimension) :=
        prod_map_fiber_first volume (volumePi dimension) volumeSFinite (volumePiSFinite dimension)
          (fun point value => add (shift point) value) shearMeasurable
          (fun point set setMeasurable =>
            preimage_of_map_eq (translate_measurable (shift point))
              (map_volume_translate (shift point)) setMeasurable)
      -- Applying `T` to the rest.
      have lowered : Measure.smul (scaleJacobian (Matrix.det rest))
          ((Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map _ lowerMeasurable) =
          Measure.prod volume (volumePi dimension) (volumePiSFinite dimension) := by
        change Measure.smul _ (Measure.map (Measure.prod _ _ _) _ _) = _
        rw [Measure.prod_map _ _ _ _ _ (MeasurableMap.identity _) (apply_measurable rest),
          Measure.map_id,
          ← Measure.prod_smul_right _ _ _ _ (((volumePiSFinite dimension).map _
            (apply_measurable rest)).smul _ (scaleJacobian_finite _)),
          Measure.prod_congr_right _ _ (volumePiSFinite dimension)
            (smul_map_volumePi_upperTriangular upper.tail restNonzero)]
      calc
        Measure.smul (scaleJacobian (Matrix.det matrix))
            ((volumePi (dimension + 1)).map (Matrix.apply matrix) (apply_measurable matrix)) =
            Measure.smul (scaleJacobian (Matrix.det rest))
              (Measure.smul (scaleJacobian leading)
                ((((((Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map _ stretchMeasurable).map _ shearMeasurable).map _
                  lowerMeasurable).map (finCons dimension) (finCons_measurable dimension)))) := by
          rw [Matrix.det_succ_of_upperTriangular upper, scaleJacobian_mul, ENNReal.mul_comm,
            ← Measure.smul_smul]
          congr 2
          rw [volumePi_succ, Measure.map_comp, Measure.map_comp, Measure.map_comp, Measure.map_comp]
          exact Measure.map_congr_function _ _ _ (funext fun pair => congrFun commute pair)
        _ = Measure.smul (scaleJacobian (Matrix.det rest))
              ((((Measure.smul (scaleJacobian leading) ((Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map _ stretchMeasurable)).map _
                shearMeasurable).map _ lowerMeasurable).map (finCons dimension) (finCons_measurable dimension)) := by
          rw [Measure.map_smul, Measure.map_smul, Measure.map_smul]
        _ = (Measure.smul (scaleJacobian (Matrix.det rest))
              ((Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map _ lowerMeasurable)).map (finCons dimension) (finCons_measurable dimension) := by
          rw [stretched, sheared, Measure.map_smul]
        _ = volumePi (dimension + 1) := by
          rw [lowered, volumePi_succ]

/-- Volume weighted by the Jacobian `|det R|` and pushed through an upper
triangular `R` with nonzero determinant is volume. -/
theorem map_withDensity_volumePi_upperTriangular {dimension : Nat}
    {matrix : Matrix.carrier dimension dimension} (upper : UpperTriangular matrix)
    (nonzero : Matrix.det matrix ≠ zero) :
    ((volumePi dimension).withDensity (fun _ => scaleJacobian (Matrix.det matrix))).map
        (Matrix.apply matrix) (apply_measurable matrix) =
      volumePi dimension := by
  rw [Measure.withDensity_const, Measure.map_smul]
  exact smul_map_volumePi_upperTriangular upper nonzero

/-- `λ(R E) = |det R| · λ(E)` for an upper triangular `R` with nonzero
determinant and a measurable `E`. -/
theorem volumePi_image_upperTriangular {dimension : Nat}
    {matrix : Matrix.carrier dimension dimension} (upper : UpperTriangular matrix)
    (nonzero : Matrix.det matrix ≠ zero) {set : Set (Fin dimension → Carrier)}
    (measurable : (Space.pi (fun _ : Fin dimension => borel)).Measurable set) :
    volumePi dimension (fun point => ∃ source, set source ∧ Matrix.apply matrix source = point) =
      ENNReal.mul (scaleJacobian (Matrix.det matrix)) (volumePi dimension set) := by
  have diagonal := (Matrix.det_ne_zero_iff upper).mp nonzero
  have image : (fun point => ∃ source, set source ∧ Matrix.apply matrix source = point) =
      Set.preimage (Matrix.solve matrix) set := by
    funext point
    apply propext
    constructor
    · rintro ⟨source, member, rfl⟩
      change set (Matrix.solve matrix (Matrix.apply matrix source))
      rwa [Matrix.solve_apply upper diagonal]
    · intro member
      exact ⟨Matrix.solve matrix point, member, Matrix.apply_solve upper diagonal point⟩
  have imageMeasurable := solve_measurable matrix measurable
  have back : Set.preimage (Matrix.apply matrix) (Set.preimage (Matrix.solve matrix) set) = set := by
    funext point
    change set (Matrix.solve matrix (Matrix.apply matrix point)) = set point
    rw [Matrix.solve_apply upper diagonal]
  refine (congrArg (fun region => volumePi dimension region) image).trans ?_
  conv => lhs; rw [← smul_map_volumePi_upperTriangular upper nonzero]
  rw [Measure.smul_apply_measurable _ _ imageMeasurable]
  congr 1
  exact (Measure.map_apply (volumePi dimension) (Matrix.apply matrix) (apply_measurable matrix)
    imageMeasurable).trans (by rw [back])

end

end Problib.Measure.Real
