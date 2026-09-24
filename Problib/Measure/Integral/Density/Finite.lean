module

public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Additive.SFinite
public import Problib.Real.Series.Basis

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Integrating a density bounded uniformly by a finite constant on a measurable
region of finite reference measure yields finite weighted mass.

The bound requires neither global finiteness of the reference measure nor
measurability of the density. -/
public theorem withDensity_finite_of_bounded {reference : Measure space}
    (density : alpha → ENNReal)
    {region : Set alpha} (measurable : space.Measurable region)
    (regionFinite : ENNReal.Finite (reference region))
    {bound : ENNReal} (boundFinite : ENNReal.Finite bound)
    (bounded : ∀ value, region value → ENNReal.le (density value) bound) :
    ENNReal.Finite ((reference.withDensity density) region) := by
  rw [reference.withDensity_apply density measurable]
  have upper := lintegral_mono_ae
    ((reference.ae_restrict_mem measurable).mono bounded)
  rw [lintegral_const, reference.restrict_apply_univ] at upper
  exact ENNReal.finite_of_le upper (ENNReal.mul_finite boundFinite regionFinite)

/-- Given a finite reference measure and a measurable density, restricting the
weighted measure to points where the density is finite yields a sigma-finite
measure.

Rational level sets cover the finite-value points, with excluded infinite-value
points adjoined to each set to span the carrier. -/
public noncomputable def withDensity_sigmaFinite_restrict_ne_top {reference : Measure space}
    (finite : Measure.IsFinite reference) {density : alpha → ENNReal}
    (measurable : ENNRealMeasurable space density) :
    Measure.SigmaFinite ((reference.withDensity density).restrict
      (fun value => density value ≠ ENNReal.top)) := by
  let infinity := fun value => density value = ENNReal.top
  have infinityMeasurable : space.Measurable infinity :=
    measurable.eq_set (ENNRealMeasurable.constant space ENNReal.top)
  let cover := fun index value => infinity value ∨
    ENNReal.le (density value) (ENNReal.rationalBasis index)
  have coverMeasurable : ∀ index, space.Measurable (cover index) :=
    fun index => space.union infinityMeasurable
      (measurable.le_set (ENNRealMeasurable.constant space (ENNReal.rationalBasis index)))
  apply Measure.SigmaFinite.ofCover
  refine { sets := cover, measurable := coverMeasurable, finite := ?_, cover := ?_ }
  · intro index
    rw [(reference.withDensity density).restrict_apply _ (coverMeasurable index)]
    apply withDensity_finite_of_bounded density
      (space.inter (coverMeasurable index) (space.complement infinityMeasurable))
      (finite.apply _) (ENNReal.rationalBasis_finite index)
    intro value member
    exact member.1.elim (fun equal => False.elim (member.2 equal)) id
  · apply Set.ext
    intro value
    constructor
    · intro _
      exact True.intro
    · intro _
      classical
      by_cases infinite : infinity value
      · exact ⟨0, Or.inl infinite⟩
      · have below : ENNReal.lt (density value) ENNReal.top :=
          ⟨ENNReal.le_top _, fun reverse => infinite (ENNReal.top_le_iff.mp reverse)⟩
        rcases ENNReal.exists_rationalBasis_between below with ⟨index, included, _⟩
        exact ⟨index, Or.inr included.1⟩

end Problib.Measure.Measure
