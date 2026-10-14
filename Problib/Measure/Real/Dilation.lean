module

public import Problib.Measure.Real.Simplex
public import Problib.Measure.Real.Scale
public import Problib.Real.Extended.Power
import Problib.Measure.Kernel.Product
import Problib.Measure.Kernel.Measurable
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Real.Grind

/-! # Dilating product volume and reading off its total

Two changes of variables on product Lebesgue measure, each reduced to the line.

- **Dilation.** Scaling every coordinate by a positive `s` multiplies volume in
  `dimension` coordinates by `s^-dimension`. Read through integrals, an integral
  is `s^dimension` times the integral of the dilated integrand
  (`lintegral_volumePi_scale`). The proof peels one coordinate per dimension, in
  the order `volumePi_succ` prepends them, and scales that coordinate on the
  line.
- **Total.** The coordinates' sum can replace the leading coordinate
  (`lintegral_volumePi_total`). Integrate the leading coordinate innermost,
  translate it by the sum of the others, and swap the order back.

Together they carry an integral over `dimension + 1` coordinates to the total
`s` and the free coordinates of the simplex scaled by `s`, the change of
variables behind normalized independent draws.
-/

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction.Dedekind

public section

/-- Scale every coordinate by `factor`. -/
@[expose] public noncomputable def scalePi (dimension : Nat) (factor : Carrier) (point : Fin dimension → Carrier) :
    Fin dimension → Carrier :=
  fun index => mul factor (point index)

public theorem scalePi_measurable (dimension : Nat) (factor : Carrier) :
    MeasurableMap (Space.pi (fun _ : Fin dimension => borel))
      (Space.pi (fun _ : Fin dimension => borel)) (scalePi dimension factor) :=
  Space.pi_measurable (fun index =>
    MeasurableMap.comp (scale_measurable_any factor)
      (Space.coordinate_measurable (fun _ : Fin dimension => borel) index))

/-- Scaling the coordinates scales their sum. -/
public theorem finSum_scalePi : (dimension : Nat) → (factor : Carrier) →
    (point : Fin dimension → Carrier) →
    additiveLaws.finSum dimension (scalePi dimension factor point) =
      mul factor (additiveLaws.finSum dimension point)
  | 0, factor, _ => (mul_zero factor).symm
  | dimension + 1, factor, point => by
      show add (mul factor (point 0))
          (additiveLaws.finSum dimension (scalePi dimension factor (finTail dimension point))) =
        mul factor (add (point 0) (additiveLaws.finSum dimension (finTail dimension point)))
      rw [finSum_scalePi dimension factor (finTail dimension point)]
      real_grind

/-- Prepending a coordinate commutes with scaling. -/
public theorem scalePi_finCons (dimension : Nat) (factor : Carrier)
    (pair : Carrier × (Fin dimension → Carrier)) :
    scalePi (dimension + 1) factor (finCons dimension pair) =
      finCons dimension (mul factor pair.1, scalePi dimension factor pair.2) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro earlier
    rfl

/-- Integrating against the line is `s` times integrating the integrand scaled
by `s`, at a positive `s`. -/
public theorem lintegral_volume_dilate {factor : Carrier} (positive : lt zero factor)
    {integrand : Carrier → ENNReal} (measurable : ENNRealMeasurable borel integrand) :
    lintegral volume integrand =
      ENNReal.mul (ENNReal.ofReal factor)
        (lintegral volume (fun value => integrand (mul factor value))) := by
  rw [lintegral_volume_scale factor positive measurable, ← ENNReal.mul_assoc,
    ofReal_mul_ofReal_inverse positive, ENNReal.one_mul]

/-- Integrating against volume in `dimension` coordinates is `s^dimension` times
integrating the integrand dilated by `s`, at a positive `s`. -/
public theorem lintegral_volumePi_scale : (dimension : Nat) → {factor : Carrier} →
    lt zero factor → {integrand : (Fin dimension → Carrier) → ENNReal} →
    ENNRealMeasurable (Space.pi (fun _ : Fin dimension => borel)) integrand →
    lintegral (volumePi dimension) integrand =
      ENNReal.mul (ENNReal.pow (ENNReal.ofReal factor) dimension)
        (lintegral (volumePi dimension) (fun point => integrand (scalePi dimension factor point)))
  | 0, factor, _, integrand, _ => by
      rw [ENNReal.pow_zero, ENNReal.one_mul]
      apply lintegral_congr
      intro point
      congr 1
      funext index
      exact Fin.elim0 index
  | dimension + 1, factor, positive, integrand, measurable => by
      have joint := measurable.comp (finCons_measurable dimension)
      have scaledJoint : ENNRealMeasurable
          (Space.product borel (Space.pi (fun _ : Fin dimension => borel)))
          (fun pair => integrand (finCons dimension (pair.1, scalePi dimension factor pair.2))) :=
        measurable.comp (MeasurableMap.comp (finCons_measurable dimension)
          (Space.product_map (MeasurableMap.identity borel) (scalePi_measurable dimension factor)))
      have column : ∀ value : Carrier,
          lintegral (volumePi dimension) (fun rest => integrand (finCons dimension (value, rest))) =
            ENNReal.mul (ENNReal.pow (ENNReal.ofReal factor) dimension)
              (lintegral (volumePi dimension) (fun rest =>
                integrand (finCons dimension (value, scalePi dimension factor rest)))) :=
        fun value => lintegral_volumePi_scale dimension positive
          (joint.comp (Space.pair_measurable (MeasurableMap.constant _ borel value)
            (MeasurableMap.identity _)))
      have inner : ENNRealMeasurable borel (fun value =>
          lintegral (volumePi dimension) (fun rest =>
            integrand (finCons dimension (value, scalePi dimension factor rest)))) :=
        Kernel.lintegral_measurable_joint (Kernel.const borel (volumePi dimension))
          (Kernel.IsSFinite.const borel (volumePiSFinite dimension)) scaledJoint
      have dilated : MeasurableMap _ _ (scalePi (dimension + 1) factor) :=
        scalePi_measurable (dimension + 1) factor
      rw [volumePi_succ, lintegral_map _ _ _ measurable,
        lintegral_map _ _ _ (measurable.comp dilated),
        lintegral_prod _ _ _ joint,
        lintegral_prod _ _ _ (measurable.comp (MeasurableMap.comp dilated
          (finCons_measurable dimension)))]
      simp only [scalePi_finCons]
      rw [lintegral_congr _ column, lintegral_smul _ _ inner,
        lintegral_volume_dilate positive inner, ENNReal.pow_succ, ← ENNReal.mul_assoc,
        ENNReal.mul_comm (ENNReal.pow _ dimension)]

/-- The coordinates' sum can replace the leading coordinate: integrating over
`dimension + 1` coordinates is integrating over the total `s` and the free
coordinates `t`, with leading coordinate `s - Σt`. -/
public theorem lintegral_volumePi_total (dimension : Nat)
    {integrand : (Fin (dimension + 1) → Carrier) → ENNReal}
    (measurable : ENNRealMeasurable (Space.pi (fun _ : Fin (dimension + 1) => borel)) integrand) :
    lintegral (volumePi (dimension + 1)) integrand =
      lintegral volume (fun total => lintegral (volumePi dimension) (fun rest =>
        integrand (finCons dimension (add (neg (additiveLaws.finSum dimension rest)) total, rest)))) := by
  have joint := measurable.comp (finCons_measurable dimension)
  have shifted : ENNRealMeasurable
      (Space.product borel (Space.pi (fun _ : Fin dimension => borel)))
      (fun pair => integrand (finCons dimension
        (add (neg (additiveLaws.finSum dimension pair.2)) pair.1, pair.2))) :=
    measurable.comp (MeasurableMap.comp (finCons_measurable dimension)
      (Space.pair_measurable
        (measurable_add (MeasurableMap.comp neg_measurable
          (MeasurableMap.comp (finSum_measurable dimension) (Space.second_measurable _ _)))
          (Space.first_measurable _ _))
        (Space.second_measurable _ _)))
  have translated : ∀ rest : Fin dimension → Carrier,
      lintegral volume (fun value => integrand (finCons dimension (value, rest))) =
        lintegral volume (fun total => integrand (finCons dimension
          (add (neg (additiveLaws.finSum dimension rest)) total, rest))) :=
    fun rest => (lintegral_volume_translate (neg (additiveLaws.finSum dimension rest))
      (joint.comp (Space.pair_measurable (MeasurableMap.identity borel)
        (MeasurableMap.constant _ _ rest)))).symm
  rw [volumePi_succ, lintegral_map _ _ _ measurable,
    lintegral_prod_symm _ _ volumeSFinite (volumePiSFinite dimension) joint,
    lintegral_congr _ translated,
    lintegral_lintegral_swap (volumePi dimension) volume (volumePiSFinite dimension) volumeSFinite
      (function := fun pair => integrand (finCons dimension
        (add (neg (additiveLaws.finSum dimension pair.1)) pair.2, pair.1)))
      (shifted.comp (Space.swap_measurable _ _))]

end

end Problib.Measure.Real
