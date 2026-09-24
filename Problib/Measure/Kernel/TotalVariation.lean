module

public import Problib.Measure.TotalVariation
public import Problib.Measure.Kernel.Composition
public import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Extended.Algebra.Binary

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

variable {α : Type u} {β : Type v}
  {source : Space α} {target : Space β}

/-- Binding probability laws through a Markov kernel cannot increase total
variation. -/
public theorem totalVariation_bind (kernel : Kernel source target)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (μ ν : Giry.Law source) :
    ENNReal.le
      (Giry.Law.totalVariation
        ⟨μ.val.bind kernel, μ.property.bind kernel markov⟩
        ⟨ν.val.bind kernel, ν.property.bind kernel markov⟩)
      (Giry.Law.totalVariation μ ν) := by
  unfold Giry.Law.totalVariation
  apply ENNReal.supremum_le
  rintro distance ⟨event, eventMeasurable, rfl⟩
  change ENNReal.le
    (ENNReal.max
      (ENNReal.sub (μ.val.bind kernel event) (ν.val.bind kernel event))
      (ENNReal.sub (ν.val.bind kernel event) (μ.val.bind kernel event)))
    (Giry.Law.totalVariation μ ν)
  rw [Measure.bind_apply μ.val kernel eventMeasurable,
    Measure.bind_apply ν.val kernel eventMeasurable]
  exact Giry.Law.lintegral_distance_le_totalVariation μ ν
    (kernel.measurable eventMeasurable)
    (fun input => (markov input).apply_le_one event)

end Problib.Measure.Kernel

namespace Problib.Measure.Giry.Law

open Problib.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Pushing two laws forward along one measurable map cannot increase their
total variation: each event downstream is the preimage of a measurable event
upstream. -/
public theorem totalVariation_map (function : α → β)
    (measurable : MeasurableMap source target function) (μ ν : Giry.Law source) :
    ENNReal.le
      (totalVariation (⟨μ.val.map function measurable, μ.property.map function measurable⟩ : Giry.Law target)
        ⟨ν.val.map function measurable, ν.property.map function measurable⟩)
      (totalVariation μ ν) := by
  unfold totalVariation
  apply ENNReal.supremum_le
  rintro distance ⟨event, eventMeasurable, rfl⟩
  apply ENNReal.le_supremum
  refine ⟨Set.preimage function event, measurable eventMeasurable, ?_⟩
  change ENNReal.max
      (ENNReal.sub (μ.val.map function measurable event) (ν.val.map function measurable event))
      (ENNReal.sub (ν.val.map function measurable event) (μ.val.map function measurable event)) = _
  rw [μ.val.map_apply function measurable eventMeasurable,
    ν.val.map_apply function measurable eventMeasurable]

/-- Total variation between a mixture and a fixed law is at most the average
total variation of the mixed laws. The lower integral needs no measurability
of the averaged distance. -/
public theorem totalVariation_bind_le (ρ : Giry.Law source) (kernel : Kernel source target)
    (markov : ∀ input, Measure.IsProbability (kernel input)) (ν : Giry.Law target) :
    ENNReal.le
      (totalVariation ⟨ρ.val.bind kernel, ρ.property.bind kernel markov⟩ ν)
      (lintegral ρ.val (fun input => totalVariation ⟨kernel input, markov input⟩ ν)) := by
  unfold totalVariation
  apply ENNReal.supremum_le
  rintro distance ⟨event, eventMeasurable, rfl⟩
  have eventMass : ENNRealMeasurable source (fun input => kernel input event) :=
    kernel.measurable eventMeasurable
  have constantMass : ENNRealMeasurable source (fun _ : α => ν.val event) :=
    ENNRealMeasurable.constant source _
  have average : lintegral ρ.val (fun _ : α => ν.val event) = ν.val event := by
    rw [lintegral_const, ρ.property.univ_eq_one, ENNReal.mul_one]
  have bound : ∀ input,
      ENNReal.le
        (ENNReal.max (ENNReal.sub (kernel input event) (ν.val event))
          (ENNReal.sub (ν.val event) (kernel input event)))
        (totalVariation ⟨kernel input, markov input⟩ ν) :=
    fun input => ENNReal.le_supremum ⟨event, eventMeasurable, rfl⟩
  change ENNReal.le
    (ENNReal.max
      (ENNReal.sub (ρ.val.bind kernel event) (ν.val event))
      (ENNReal.sub (ν.val event) (ρ.val.bind kernel event))) _
  rw [Measure.bind_apply ρ.val kernel eventMeasurable]
  apply ENNReal.max_le
  · -- ∫ a ≤ ∫ (sub a b + b) = ∫ sub a b + b.
    apply ENNReal.sub_le_iff_le_add.mpr
    have split := lintegral_mono ρ.val
      (fun input => ENNReal.le_sub_add (kernel input event) (ν.val event))
    rw [lintegral_add ρ.val (ENNRealMeasurable.sub eventMass constantMass) constantMass,
      average] at split
    refine ENNReal.le_trans split (ENNReal.add_le_add_right ?_ _)
    exact lintegral_mono ρ.val fun input =>
      ENNReal.le_trans (ENNReal.le_max_left _ _) (bound input)
  · -- b = ∫ b ≤ ∫ (sub b a + a) = ∫ sub b a + ∫ a.
    apply ENNReal.sub_le_iff_le_add.mpr
    have split := lintegral_mono ρ.val
      (fun input => ENNReal.le_sub_add (ν.val event) (kernel input event))
    rw [lintegral_add ρ.val (ENNRealMeasurable.sub constantMass eventMass) eventMass,
      average] at split
    refine ENNReal.le_trans split (ENNReal.add_le_add_right ?_ _)
    exact lintegral_mono ρ.val fun input =>
      ENNReal.le_trans (ENNReal.le_max_right _ _) (bound input)

end Problib.Measure.Giry.Law
