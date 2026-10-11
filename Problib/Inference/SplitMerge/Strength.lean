module

public import Problib.Measure.Equivalence.Preserving
public import Problib.Measure.Equivalence.Partial
public import Problib.Measure.Real.Affine
public import Problib.Measure.Real.Order
public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Kernel.Product

set_option autoImplicit false

/-!
# Splitting a strength

A positive strength `α` and a fraction `v` in the unit interval split into two
positive strengths `(vα, (1 − v)α)`. The inverse adds the strengths and reads
the fraction off the first. Against Lebesgue volume on both planes, the split
changes the reference by `1 / (α₁ + α₂)` (`strengthSplit_reference_change`).

The proof integrates over `v` at fixed `α`, where `α₁ = αv` rescales volume by
`1 / α`. It then swaps the order and substitutes `α = α₁ + α₂` at fixed `α₁`.
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel volume volumeSFinite measurable_add measurable_sub
  measurable_mul measurable_div measurable_lt ofReal_measurable inverse_measurable
  lintegral_volume_scale lintegral_volume_translate)

public section

/-- The plane of two strengths, or of a strength and a fraction. -/
abbrev strengthPlane : Space (Carrier × Carrier) := Space.product borel borel

/-- Lebesgue volume on the plane. -/
@[expose] noncomputable def planeVolume : Measure strengthPlane :=
  Measure.prod volume volume volumeSFinite

/-- The first coordinate of the plane is measurable. -/
theorem planeFirst_measurable : MeasurableMap strengthPlane borel (fun point => point.1) :=
  Space.first_measurable borel borel

/-- The second coordinate of the plane is measurable. -/
theorem planeSecond_measurable : MeasurableMap strengthPlane borel (fun point => point.2) :=
  Space.second_measurable borel borel

/-- A constant on the plane is measurable. -/
theorem planeConstant_measurable (value : Carrier) :
    MeasurableMap strengthPlane borel (fun _ => value) :=
  MeasurableMap.constant strengthPlane borel value

/-- Split a positive strength by a fraction in the unit interval. -/
@[expose] noncomputable def strengthSplit :
    MeasurablePartialEquivalence strengthPlane strengthPlane where
  forward := fun point =>
    (Dedekind.mul point.2 point.1, Dedekind.mul (Dedekind.sub Dedekind.one point.2) point.1)
  inverse := fun point =>
    (Dedekind.add point.1 point.2,
      Dedekind.div point.1 (Dedekind.add point.1 point.2))
  sourceDomain := fun point => Dedekind.lt Dedekind.zero point.1 ∧
    Dedekind.lt Dedekind.zero point.2 ∧ Dedekind.lt point.2 Dedekind.one
  targetDomain := fun point => Dedekind.lt Dedekind.zero point.1 ∧
    Dedekind.lt Dedekind.zero point.2
  sourceMeasurable := strengthPlane.inter
    (measurable_lt (planeConstant_measurable _) planeFirst_measurable)
    (strengthPlane.inter (measurable_lt (planeConstant_measurable _) planeSecond_measurable)
      (measurable_lt planeSecond_measurable (planeConstant_measurable _)))
  targetMeasurable := strengthPlane.inter
    (measurable_lt (planeConstant_measurable _) planeFirst_measurable)
    (measurable_lt (planeConstant_measurable _) planeSecond_measurable)
  forward_mem := by
    rintro ⟨strength, fraction⟩ ⟨strengthPositive, fractionPositive, fractionBelow⟩
    exact ⟨Dedekind.mul_positive fractionPositive strengthPositive,
      Dedekind.mul_positive (Dedekind.sub_positive_iff.mpr fractionBelow) strengthPositive⟩
  inverse_mem := by
    rintro ⟨first, second⟩ ⟨firstPositive, secondPositive⟩
    have sumPositive := Dedekind.add_positive firstPositive secondPositive
    have less : Dedekind.lt first (Dedekind.add first second) := by
      apply Dedekind.sub_positive_iff.mp
      rw [Dedekind.add_sub_self]
      exact secondPositive
    refine ⟨sumPositive, Dedekind.div_positive firstPositive sumPositive, ?_⟩
    rw [← Dedekind.div_self (Dedekind.nonzero_of_positive firstPositive)]
    exact Dedekind.div_lt_div_of_positive firstPositive firstPositive less
  inverse_forward := by
    rintro ⟨strength, fraction⟩ ⟨strengthPositive, _, _⟩
    have sum : Dedekind.add (Dedekind.mul fraction strength)
        (Dedekind.mul (Dedekind.sub Dedekind.one fraction) strength) = strength := by
      rw [← Dedekind.add_mul, Dedekind.add_sub_cancel, Dedekind.one_mul]
    apply Prod.ext
    · exact sum
    · change Dedekind.div (Dedekind.mul fraction strength)
          (Dedekind.add (Dedekind.mul fraction strength)
            (Dedekind.mul (Dedekind.sub Dedekind.one fraction) strength)) = fraction
      rw [sum, Dedekind.div_eq_mul_inverse, Dedekind.mul_assoc,
        Dedekind.mul_inverse_cancel_of_positive strengthPositive, Dedekind.mul_one]
  forward_inverse := by
    rintro ⟨first, second⟩ ⟨firstPositive, secondPositive⟩
    have sumNonzero := Dedekind.nonzero_of_positive
      (Dedekind.add_positive firstPositive secondPositive)
    apply Prod.ext
    · exact Dedekind.div_mul_cancel first sumNonzero
    · change Dedekind.mul (Dedekind.sub Dedekind.one
          (Dedekind.div first (Dedekind.add first second))) (Dedekind.add first second) = second
      rw [Dedekind.sub_mul, Dedekind.one_mul, Dedekind.div_mul_cancel first sumNonzero,
        Dedekind.add_sub_self]
  forwardMeasurable := Space.pair_measurable
    (measurable_mul planeSecond_measurable planeFirst_measurable)
    (measurable_mul (measurable_sub (planeConstant_measurable _) planeSecond_measurable)
      planeFirst_measurable)
  inverseMeasurable := Space.pair_measurable
    (measurable_add planeFirst_measurable planeSecond_measurable)
    (measurable_div planeFirst_measurable
      (measurable_add planeFirst_measurable planeSecond_measurable))

/-- The split's Jacobian, read on the two-strength side. -/
@[expose] noncomputable def strengthJacobian (point : Carrier × Carrier) : Carrier :=
  Dedekind.inverse (Dedekind.add point.1 point.2)

theorem strengthJacobian_measurable :
    MeasurableMap strengthPlane borel strengthJacobian :=
  MeasurableMap.comp inverse_measurable
    (measurable_add planeFirst_measurable planeSecond_measurable)

/-- The inner integrand after the fraction is rescaled to the first strength:
the first strength lies below the parent, with the parent's reciprocal. -/
private noncomputable def rescaled (function : Carrier × Carrier → ENNReal)
    (point : Carrier × Carrier) : ENNReal :=
  ennrealIndicator
    (fun point : Carrier × Carrier => Dedekind.lt Dedekind.zero point.2 ∧
      Dedekind.lt point.2 point.1)
    (fun point => ENNReal.mul (ENNReal.ofReal (Dedekind.inverse point.1))
      (function (point.2, Dedekind.sub point.1 point.2))) point

private theorem rescaled_measurable {function : Carrier × Carrier → ENNReal}
    (functionMeasurable : ENNRealMeasurable strengthPlane function) :
    ENNRealMeasurable strengthPlane (rescaled function) :=
  ENNRealMeasurable.indicator
    (strengthPlane.inter (measurable_lt (planeConstant_measurable _) planeSecond_measurable)
      (measurable_lt planeSecond_measurable planeFirst_measurable))
    (ENNRealMeasurable.mul
      (ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
        (MeasurableMap.comp inverse_measurable planeFirst_measurable))
      (ENNRealMeasurable.comp functionMeasurable
        (Space.pair_measurable planeSecond_measurable
          (measurable_sub planeFirst_measurable planeSecond_measurable))))

private theorem indicator_apply {β : Type} (region : Set β) (function : β → ENNReal)
    (point : β) [Decidable (region point)] :
    ennrealIndicator region function point =
      if region point then function point else ENNReal.zero := by
  unfold ennrealIndicator ennrealPiecewise
  by_cases member : region point
  · rw [ite_eq_left member, ite_eq_left member]
  · rw [ite_eq_right member, ite_eq_right member]

/-- At a fixed parent strength, integrating over the fraction is integrating
over the first strength below the parent, weighted by the parent's reciprocal. -/
private theorem fraction_rescale {function : Carrier × Carrier → ENNReal}
    (functionMeasurable : ENNRealMeasurable strengthPlane function) (strength : Carrier) :
    lintegral volume (fun fraction =>
        ennrealIndicator strengthSplit.sourceDomain
          (fun point => function (strengthSplit.forward point)) (strength, fraction)) =
      lintegral volume (fun first => rescaled function (strength, first)) := by
  classical
  have sectionMeasurable : ENNRealMeasurable borel
      (fun first => rescaled function (strength, first)) :=
    ENNRealMeasurable.comp (rescaled_measurable functionMeasurable)
      (Space.pair_measurable (MeasurableMap.constant _ _ strength) (MeasurableMap.identity _))
  by_cases strengthPositive : Dedekind.lt Dedekind.zero strength
  · let below : Carrier → ENNReal := fun first =>
      ennrealIndicator (fun first => Dedekind.lt Dedekind.zero first ∧ Dedekind.lt first strength)
        (fun first => function (first, Dedekind.sub strength first)) first
    have belowMeasurable : ENNRealMeasurable borel below :=
      ENNRealMeasurable.indicator
        (borel.inter
          (measurable_lt (MeasurableMap.constant _ _ _) (MeasurableMap.identity _))
          (measurable_lt (MeasurableMap.identity _) (MeasurableMap.constant _ _ _)))
        (ENNRealMeasurable.comp functionMeasurable
          (Space.pair_measurable (MeasurableMap.identity _)
            (measurable_sub (MeasurableMap.constant _ _ _) (MeasurableMap.identity _))))
    have scaled : ∀ fraction : Carrier,
        ennrealIndicator strengthSplit.sourceDomain
          (fun point => function (strengthSplit.forward point)) (strength, fraction) =
        below (Dedekind.mul strength fraction) := by
      intro fraction
      have lower : Dedekind.lt Dedekind.zero fraction ↔
          Dedekind.lt Dedekind.zero (Dedekind.mul strength fraction) := by
        have scaled := Dedekind.mul_lt_mul_left_iff strengthPositive
          (left := Dedekind.zero) (right := fraction)
        rw [Dedekind.mul_zero] at scaled
        exact scaled.symm
      have upper : Dedekind.lt fraction Dedekind.one ↔
          Dedekind.lt (Dedekind.mul strength fraction) strength := by
        have scaled := Dedekind.mul_lt_mul_left_iff strengthPositive
          (left := fraction) (right := Dedekind.one)
        rw [Dedekind.mul_one] at scaled
        exact scaled.symm
      have image : strengthSplit.forward (strength, fraction) =
          (Dedekind.mul strength fraction,
            Dedekind.sub strength (Dedekind.mul strength fraction)) := by
        change (Dedekind.mul fraction strength,
            Dedekind.mul (Dedekind.sub Dedekind.one fraction) strength) = _
        rw [Dedekind.mul_comm fraction strength, Dedekind.sub_mul, Dedekind.one_mul,
          Dedekind.mul_comm fraction strength]
      dsimp only [below]
      rw [indicator_apply, indicator_apply]
      by_cases inside : strengthSplit.sourceDomain (strength, fraction)
      · have inside' : Dedekind.lt Dedekind.zero (Dedekind.mul strength fraction) ∧
            Dedekind.lt (Dedekind.mul strength fraction) strength :=
          ⟨lower.mp inside.2.1, upper.mp inside.2.2⟩
        rw [ite_eq_left inside, ite_eq_left inside', image]
      · have outside' : ¬ (Dedekind.lt Dedekind.zero (Dedekind.mul strength fraction) ∧
            Dedekind.lt (Dedekind.mul strength fraction) strength) := by
          rintro ⟨positive, less⟩
          exact inside ⟨strengthPositive, lower.mpr positive, upper.mpr less⟩
        rw [ite_eq_right inside, ite_eq_right outside']
    have weighted : ∀ first : Carrier, rescaled function (strength, first) =
        ENNReal.mul (ENNReal.ofReal (Dedekind.inverse strength)) (below first) := by
      intro first
      unfold rescaled
      dsimp only [below]
      rw [indicator_apply, indicator_apply]
      by_cases inside : Dedekind.lt Dedekind.zero first ∧ Dedekind.lt first strength
      · rw [ite_eq_left inside, ite_eq_left inside]
      · rw [ite_eq_right inside, ite_eq_right inside, ENNReal.mul_zero]
    rw [lintegral_congr _ scaled, lintegral_volume_scale strength strengthPositive belowMeasurable,
      lintegral_congr _ weighted, lintegral_smul _ _ belowMeasurable]
  · have leftZero : ∀ fraction : Carrier,
        ennrealIndicator strengthSplit.sourceDomain
          (fun point => function (strengthSplit.forward point)) (strength, fraction) =
        ENNReal.zero := by
      intro fraction
      rw [indicator_apply, ite_eq_right (fun inside => strengthPositive inside.1)]
    have rightZero : ∀ first : Carrier, rescaled function (strength, first) = ENNReal.zero := by
      intro first
      unfold rescaled
      rw [indicator_apply, ite_eq_right (fun inside => strengthPositive
        (Dedekind.lt_trans inside.1 inside.2))]
    rw [lintegral_congr _ leftZero, lintegral_congr _ rightZero]

/-- At a fixed first strength, integrating over the parent is integrating over
the second strength, with the parent as their sum. -/
private theorem parent_translate {function : Carrier × Carrier → ENNReal}
    (functionMeasurable : ENNRealMeasurable strengthPlane function) (first : Carrier) :
    lintegral volume (fun strength => rescaled function (strength, first)) =
      lintegral volume (fun second =>
        ennrealIndicator strengthSplit.targetDomain
          (fun point => ENNReal.mul (ENNReal.ofReal (strengthJacobian point)) (function point))
          (first, second)) := by
  classical
  have sectionMeasurable : ENNRealMeasurable borel
      (fun strength => rescaled function (strength, first)) :=
    ENNRealMeasurable.comp (rescaled_measurable functionMeasurable)
      (Space.pair_measurable (MeasurableMap.identity _) (MeasurableMap.constant _ _ first))
  rw [← lintegral_volume_translate first sectionMeasurable]
  apply lintegral_congr
  intro second
  unfold rescaled
  rw [indicator_apply, indicator_apply]
  have difference : Dedekind.sub (Dedekind.add first second) first = second :=
    Dedekind.add_sub_self first second
  have above : Dedekind.lt first (Dedekind.add first second) ↔
      Dedekind.lt Dedekind.zero second := by
    have shifted := Dedekind.add_lt_add_left_iff (left := Dedekind.zero) (right := second)
      (shift := first)
    rw [Dedekind.add_zero] at shifted
    exact shifted
  by_cases inside : strengthSplit.targetDomain (first, second)
  · have inside' : Dedekind.lt Dedekind.zero first ∧
        Dedekind.lt first (Dedekind.add first second) := ⟨inside.1, above.mpr inside.2⟩
    rw [ite_eq_left inside', ite_eq_left inside, difference]
    rfl
  · have outside' : ¬ (Dedekind.lt Dedekind.zero first ∧
        Dedekind.lt first (Dedekind.add first second)) := by
      rintro ⟨positive, less⟩
      exact inside ⟨positive, above.mp less⟩
    rw [ite_eq_right outside', ite_eq_right inside]

/-- Splitting a strength changes planar volume by the reciprocal of the parent
strength, read on the two-strength side. -/
theorem strengthSplit_reference_change :
    strengthSplit.ReferenceChange planeVolume planeVolume strengthJacobian := by
  unfold MeasurablePartialEquivalence.ReferenceChange
  apply Measure.ext_of_lintegral
  intro function functionMeasurable
  have weightMeasurable : ENNRealMeasurable strengthPlane
      (fun point => ENNReal.ofReal (strengthJacobian point)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
      strengthJacobian_measurable
  have leftMeasurable : ENNRealMeasurable strengthPlane
      (ennrealIndicator strengthSplit.sourceDomain
        (fun point => function (strengthSplit.forward point))) :=
    ENNRealMeasurable.indicator strengthSplit.sourceMeasurable
      (ENNRealMeasurable.comp functionMeasurable strengthSplit.forwardMeasurable)
  have rightMeasurable : ENNRealMeasurable strengthPlane
      (ennrealIndicator strengthSplit.targetDomain
        (fun point => ENNReal.mul (ENNReal.ofReal (strengthJacobian point)) (function point))) :=
    ENNRealMeasurable.indicator strengthSplit.targetMeasurable
      (ENNRealMeasurable.mul weightMeasurable functionMeasurable)
  unfold planeVolume
  rw [lintegral_map _ _ _ functionMeasurable,
    ← lintegral_indicator _ _ strengthSplit.sourceMeasurable,
    lintegral_withDensity _ weightMeasurable functionMeasurable,
    ← lintegral_indicator _ _ strengthSplit.targetMeasurable,
    lintegral_prod _ _ volumeSFinite leftMeasurable,
    lintegral_prod _ _ volumeSFinite rightMeasurable,
    lintegral_congr _ (fraction_rescale functionMeasurable),
    ← lintegral_prod _ _ volumeSFinite (rescaled_measurable functionMeasurable),
    lintegral_prod_symm _ _ volumeSFinite volumeSFinite (rescaled_measurable functionMeasurable),
    lintegral_congr _ (parent_translate functionMeasurable)]

end
end Problib.Inference
