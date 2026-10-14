module

public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Integral.Lebesgue.Markov
public import Problib.Measure.Additive.SFinite
public import Problib.Real.Series.Basis
public import Problib.Measure.Integral.Lebesgue.Zero
public import Problib.Measure.Normalization

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

/-- A measurable density bounded by a finite constant against a finite reference
measure, and positive on a region of positive reference measure, has positive
finite total mass. The bound gives finiteness through
`withDensity_finite_of_bounded` at the whole carrier, and positivity on the
charged region gives a positive integral through `lintegral_positive`. -/
public theorem withDensity_isNormalizable_of_bounded {reference : Measure space}
    (finite : IsFinite reference) {density : alpha → ENNReal}
    (measurable : ENNRealMeasurable space density)
    {bound : ENNReal} (boundFinite : ENNReal.Finite bound)
    (bounded : ∀ value, ENNReal.le (density value) bound)
    {region : Set alpha} (charged : ENNReal.lt ENNReal.zero (reference region))
    (positive : ∀ value, region value → ENNReal.lt ENNReal.zero (density value)) :
    IsNormalizable (reference.withDensity density) where
  finite := ⟨withDensity_finite_of_bounded density space.univ finite.univ_finite boundFinite
    fun value _ => bounded value⟩
  nonzero := by
    rw [reference.withDensity_apply density space.univ, reference.restrict_univ]
    exact ENNReal.zero_lt_iff_ne_zero.mp
      (lintegral_positive reference charged measurable positive)

/-- A measurable density of a finite measure is finite at almost every point of
the reference, since its integral is the finite total mass. -/
public theorem finite_ae_of_density {candidate reference : Measure space}
    {density : alpha → ENNReal} (measurable : ENNRealMeasurable space density)
    (isDensity : IsDensity candidate reference density)
    (finite : ENNReal.Finite (candidate Set.univ)) :
    reference.AE (fun point => density point ≠ ENNReal.top) := by
  have total : lintegral reference density = candidate Set.univ := by
    rw [isDensity.apply space.univ, reference.restrict_univ]
  have finiteIntegral : ENNReal.Finite (lintegral reference density) := by
    rw [total]
    exact finite
  exact (ae_finite_of_lintegral_finite reference measurable finiteIntegral).mono
    fun _ finitePoint => ENNReal.finite_iff_ne_top.mp finitePoint

/-- Given a finite reference measure and a measurable density, restricting the
weighted measure to points where the density is finite yields a sigma-finite
measure.

Rational level sets cover the finite-value points, with excluded infinite-value
points adjoined to each set to span the carrier. -/
public noncomputable def withDensitySigmaFiniteRestrictNeTop {reference : Measure space}
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
