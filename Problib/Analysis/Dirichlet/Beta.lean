module

public import Problib.Analysis.Dirichlet.Gamma
public import Problib.Analysis.Beta.Density
import Problib.Measure.Kernel.Product
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Integral.Density.Change
import Problib.Real.Grind

/-! The Beta law is the Dirichlet law's first coordinate at two lanes.

At two concentrations `(a, b)` the simplex has one free coordinate `v`, and the
first coordinate is the leftover `1 - v`. Its law has density `x^(a-1) (1-x)^(b-1)`
against volume, up to the Dirichlet normalizer, after the reflection
`v = 1 - x`. Both sides are probability measures, so the normalizers agree and
the first coordinate has law `Beta.law a b` (`law_map_first`).

With `gammas_map_normalize_total` this gives the Gamma–Beta split
(`gammas_split`). For independent `X ~ Gamma(a, 1)` and `Y ~ Gamma(b, 1)`,
`X/(X+Y)` and `X+Y` are independent, with laws `Beta(a, b)` and `Gamma(a+b, 1)`.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Dirichlet

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- A measure of a measurable set is the integral of its indicator. -/
private theorem measure_eq_lintegral {α : Type} {space : Space α} (measure : Measure space)
    {set : Set α} (measurable : space.Measurable set) :
    measure set = lintegral measure (ennrealIndicator set (fun _ => ENNReal.one)) := by
  rw [lintegral_indicator _ _ measurable, lintegral_const, Measure.restrict_apply_univ,
    ENNReal.one_mul]

/-- Reading the first coordinate is measurable. -/
public theorem first_measurable (count : Nat) :
    MeasurableMap (Space.pi (fun _ : Fin (count + 1) => borel)) borel
      (fun point : Fin (count + 1) → Carrier => point 0) :=
  Space.coordinate_measurable (fun _ : Fin (count + 1) => borel) 0

/-- Integrating against the line is integrating the reflection `x ↦ 1 - x`. -/
private theorem lintegral_reflect {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral volume integrand = lintegral volume (fun value => integrand (sub one value)) := by
  have shifted : ENNRealMeasurable borel (fun value => integrand (add one value)) :=
    measurable.comp (translate_measurable one)
  rw [← lintegral_volume_translate one measurable, ← lintegral_volume_neg shifted]
  apply lintegral_congr
  intro value
  rw [sub_eq_add_neg]

/-- Volume on one coordinate is volume on the line. -/
private theorem lintegral_volumePi_one {integrand : (Fin 1 → Carrier) → ENNReal}
    (measurable : ENNRealMeasurable (Space.pi (fun _ : Fin 1 => borel)) integrand) :
    lintegral (volumePi 1) integrand =
      lintegral volume (fun value => integrand (finCons 0 (value, fun index => index.elim0))) := by
  have joint := measurable.comp (finCons_measurable 0)
  rw [volumePi_succ, lintegral_map _ _ _ measurable, lintegral_prod _ _ _ joint]
  apply lintegral_congr
  intro value
  rw [volumePi_zero, lintegral_dirac _ _ (joint.comp (Space.pair_measurable
    (MeasurableMap.constant _ borel value) (MeasurableMap.identity _)))]

/-- The first coordinate of the Dirichlet law at two lanes is volume weighted
by the Dirichlet normalizer times the Beta weight. -/
private theorem law_map_first_withDensity {concentration : Fin 2 → Carrier}
    (positive : ∀ lane, lt zero (concentration lane)) :
    (law concentration).map (fun point => point 0) (first_measurable 1) =
      volume.withDensity (fun value =>
        ENNReal.mul (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
          (Beta.weight (concentration 0) (concentration 1) one value)) := by
  classical
  apply Measure.ext
  intro set setMeasurable
  have indicator := ENNRealMeasurable.indicator setMeasurable
    (ENNRealMeasurable.constant borel ENNReal.one)
  have slice : ENNRealMeasurable (Space.pi (fun _ : Fin 2 => borel))
      (fun point : Fin 2 → Carrier => ennrealIndicator set (fun _ => ENNReal.one) (point 0)) :=
    indicator.comp (first_measurable 1)
  have reduced : ENNRealMeasurable (Space.pi (fun _ : Fin 1 => borel)) (fun free =>
      ENNReal.mul (weight 2 concentration (simplexPoint 1 free))
        (ennrealIndicator set (fun _ => ENNReal.one) (simplexPoint 1 free 0))) :=
    ((weight_measurable 2 concentration).comp (simplexPoint_measurable 1)).mul
      (slice.comp (simplexPoint_measurable 1))
  have lined : ENNRealMeasurable borel (fun value =>
      ENNReal.mul (weight 2 concentration (simplexPoint 1 (finCons 0 (value, fun index => index.elim0))))
        (ennrealIndicator set (fun _ => ENNReal.one)
          (simplexPoint 1 (finCons 0 (value, fun index => index.elim0)) 0))) :=
    reduced.comp (MeasurableMap.comp (finCons_measurable 0)
      (Space.pair_measurable (MeasurableMap.identity borel) (MeasurableMap.constant _ _ _)))
  rw [Measure.map_apply _ _ _ setMeasurable, measure_eq_lintegral _ ((first_measurable 1) setMeasurable),
    law_eq_withDensity positive]
  show lintegral _ (fun point : Fin 2 → Carrier =>
    ennrealIndicator set (fun _ => ENNReal.one) (point 0)) = _
  rw [lintegral_withDensity _ (density_measurable concentration) slice,
    lintegral_simplex 1 ((density_measurable concentration).mul slice),
    Measure.withDensity_apply _ _ setMeasurable, ← lintegral_indicator _ _ setMeasurable]
  have absorbed : ∀ free : Fin 1 → Carrier,
      ennrealIndicator (simplexRegion 1) (fun free => ENNReal.mul (density concentration
          (simplexPoint 1 free)) (ennrealIndicator set (fun _ => ENNReal.one) (simplexPoint 1 free 0)))
        free =
      ENNReal.mul (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
        (ENNReal.mul (weight 2 concentration (simplexPoint 1 free))
          (ennrealIndicator set (fun _ => ENNReal.one) (simplexPoint 1 free 0))) := by
    intro free
    by_cases member : simplexRegion 1 free
    · rw [ennrealIndicator_of_mem member]
      unfold density
      exact ENNReal.mul_assoc _ _ _
    · rw [ennrealIndicator_of_not_mem member]
      have vanishing : weight 2 concentration (simplexPoint 1 free) = ENNReal.zero :=
        simplexWeight_of_not_mem member (concentration 0) (finTail 1 concentration)
      rw [vanishing, ENNReal.zero_mul, ENNReal.mul_zero]
  rw [lintegral_congr _ absorbed, lintegral_smul _ _ reduced, lintegral_volumePi_one reduced,
    lintegral_reflect lined, ← lintegral_smul _ _ (lined.comp (measurable_sub
      (MeasurableMap.constant borel borel one) (MeasurableMap.identity borel)))]
  apply lintegral_congr
  intro value
  have leftover : sub one (additiveLaws.finSum 1
      (finCons 0 (sub one value, fun index => index.elim0))) = value := by
    show sub one (add (sub one value) zero) = value
    real_grind
  show ENNReal.mul _ (ENNReal.mul (ENNReal.mul
      (shapePower (concentration 0) (sub one (additiveLaws.finSum 1
        (finCons 0 (sub one value, fun index => index.elim0)))))
      (ENNReal.mul (shapePower (concentration 1) (sub one value)) ENNReal.one))
    (ennrealIndicator set (fun _ => ENNReal.one) (sub one (additiveLaws.finSum 1
        (finCons 0 (sub one value, fun index => index.elim0)))))) = _
  rw [leftover, ENNReal.mul_one]
  by_cases member : set value
  · rw [ennrealIndicator_of_mem member, ennrealIndicator_of_mem member, ENNReal.mul_one]
    rfl
  · rw [ennrealIndicator_of_not_mem member, ennrealIndicator_of_not_mem member, ENNReal.mul_zero,
      ENNReal.mul_zero]

/-- The Dirichlet law's first coordinate at two lanes has law
`Beta.law a b`, at positive concentrations. -/
public theorem law_map_first {concentration : Fin 2 → Carrier}
    (positive : ∀ lane, lt zero (concentration lane)) :
    (law concentration).map (fun point => point 0) (first_measurable 1) =
      Beta.law (concentration 0) (concentration 1) := by
  have weighted := law_map_first_withDensity positive
  have cancel : ENNReal.mul (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
      (Beta.family.normalizer (concentration 0, concentration 1)) = ENNReal.one := by
    have total := congrArg (fun measure : Measure borel => measure Set.univ) weighted
    rw [Measure.map_apply _ _ _ borel.univ, Set.preimage_univ,
      (law_isProbability concentration).univ_eq_one, Measure.withDensity_apply _ _ borel.univ,
      Measure.restrict_univ, lintegral_smul _ _ (Beta.weight_measurable _ _ one)] at total
    exact total.symm
  rw [weighted, Beta.law]
  exact (Beta.family.law_eq_of_scale cancel (fun _ => rfl)).symm

/-- The Gamma–Beta split. For independent `X ~ Gamma(a, 1)` and
`Y ~ Gamma(b, 1)` at positive shapes, `X/(X+Y)` and `X+Y` are independent,
with laws `Beta(a, b)` and `Gamma(a+b, 1)`. -/
public theorem gammas_split {shapes : Fin 2 → Carrier} (positive : ∀ lane, lt zero (shapes lane)) :
    (gammas 2 shapes).map
        (fun point => (div (point 0) (additiveLaws.finSum 2 point), additiveLaws.finSum 2 point))
        (Space.pair_measurable (MeasurableMap.comp (first_measurable 1) (normalize_measurable 2))
          (finSum_measurable 2)) =
      Measure.prod (Beta.law (shapes 0) (shapes 1)) (Gamma.law (additiveLaws.finSum 2 shapes) one)
        (probability_sFinite (Gamma.law_isProbability _ one)) := by
  have split := Measure.map_comp (gammas 2 shapes)
    (fun point => (normalize 2 point, additiveLaws.finSum 2 point))
    (fun pair => (pair.1 0, pair.2)) (normalizeTotal_measurable 2)
    (Space.product_map (first_measurable 1) (MeasurableMap.identity borel))
  rw [gammas_map_normalize_total positive,
    Measure.prod_map _ _ _ _ _ (first_measurable 1) (MeasurableMap.identity borel),
    law_map_first positive] at split
  rw [← Measure.prod_congr_right _ _ _ (Measure.map_id _), split]
  exact Measure.map_congr_function _ _ _ rfl

end

end Problib.Analysis.Dirichlet
