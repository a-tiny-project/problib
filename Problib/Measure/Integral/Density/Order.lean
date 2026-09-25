module

public import Problib.Measure.Additive.SFinite
public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Integral.Density.Restrict
public import Problib.Real.Series.Basis

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha} {measure : Measure space}

private theorem null_separated_set {left right : alpha → ENNReal}
    (finite : IsFinite measure)
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right)
    (included : ∀ set, space.Measurable set →
      ENNReal.le ((measure.withDensity left) set) ((measure.withDensity right) set))
    {lower upper : ENNReal} (separated : ENNReal.lt lower upper) :
    measure.NullSet (fun value =>
      ENNReal.le (right value) lower ∧ ENNReal.le upper (left value)) := by
  classical
  let region : Set alpha := fun value =>
    ENNReal.le (right value) lower ∧ ENNReal.le upper (left value)
  have regionMeasurable : space.Measurable region :=
    space.inter (rightMeasurable.iic lower) (leftMeasurable.ici upper)
  have regionFinite : ENNReal.Finite (measure region) := by
    have finiteRestriction := (finite.restrict region).univ_finite
    rw [measure.restrict_apply_univ] at finiteRestriction
    exact finiteRestriction
  have onRegion := measure.ae_restrict_mem regionMeasurable
  have lowerBound : ENNReal.le (ENNReal.mul upper (measure region))
      (lintegral (measure.restrict region) left) := by
    have bound := lintegral_mono_ae
      (Measure.AE.mono onRegion (fun _ member => member.2))
    rw [lintegral_const, measure.restrict_apply_univ] at bound
    exact bound
  have upperBound : ENNReal.le (lintegral (measure.restrict region) right)
      (ENNReal.mul lower (measure region)) := by
    have bound := lintegral_mono_ae
      (Measure.AE.mono onRegion (fun _ member => member.1))
    rw [lintegral_const, measure.restrict_apply_univ] at bound
    exact bound
  have comparison := included region regionMeasurable
  rw [measure.withDensity_apply left regionMeasurable,
    measure.withDensity_apply right regionMeasurable] at comparison
  apply Classical.byContradiction
  intro nonzero
  have cancelled := (ENNReal.mul_le_mul_right_iff regionFinite
    (ENNReal.zero_lt_iff_ne_zero.mpr nonzero)).mp
    (ENNReal.le_trans lowerBound (ENNReal.le_trans comparison upperBound))
  exact separated.2 cancelled

/-- Under a finite reference measure, ordering of density-weighted measures on
measurable sets implies almost-everywhere ordering of the measurable densities. -/
public theorem ae_le_of_withDensity_le_finite {left right : alpha → ENNReal}
    (finite : IsFinite measure)
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right)
    (included : ∀ set, space.Measurable set →
      ENNReal.le ((measure.withDensity left) set) ((measure.withDensity right) set)) :
    measure.AE (fun value => ENNReal.le (left value) (right value)) := by
  classical
  let regions : Nat → Nat → Set alpha := fun lower upper value =>
    ENNReal.lt (ENNReal.rationalBasis lower) (ENNReal.rationalBasis upper) ∧
      ENNReal.le (right value) (ENNReal.rationalBasis lower) ∧
      ENNReal.le (ENNReal.rationalBasis upper) (left value)
  have nullRegions : ∀ lower upper, measure.NullSet (regions lower upper) := by
    intro lower upper
    by_cases separated :
        ENNReal.lt (ENNReal.rationalBasis lower) (ENNReal.rationalBasis upper)
    · exact (null_separated_set finite leftMeasurable rightMeasurable
        included separated).mono (fun {_} member => member.2)
    · apply measure.null_empty.mono
      intro value member
      exact separated member.1
  apply (NullSet.iUnion (fun lower => NullSet.iUnion (nullRegions lower))).mono
  intro value notIncluded
  have less : ENNReal.lt (right value) (left value) :=
    ⟨(ENNReal.le_total (left value) (right value)).resolve_left notIncluded,
      notIncluded⟩
  rcases ENNReal.exists_rationalBasis_between less with
    ⟨lower, rightLower, lowerLeft⟩
  rcases ENNReal.exists_rationalBasis_between lowerLeft with
    ⟨upper, lowerUpper, upperLeft⟩
  exact ⟨lower, upper, lowerUpper, rightLower.1, upperLeft.1⟩

/-- Under a sigma-finite reference measure, ordering of density-weighted
measures on measurable sets implies almost-everywhere ordering of the measurable
densities. -/
public theorem ae_le_of_withDensity_le {left right : alpha → ENNReal}
    (finite : SigmaFinite measure)
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right)
    (included : ∀ set, space.Measurable set →
      ENNReal.le ((measure.withDensity left) set) ((measure.withDensity right) set)) :
    measure.AE (fun value => ENNReal.le (left value) (right value)) := by
  apply AE.of_restrict_cover finite.cover
  intro index
  have restrictionFinite : IsFinite (measure.restrict (finite.sets index)) := by
    constructor
    rw [measure.restrict_apply_univ]
    exact finite.finite index
  apply ae_le_of_withDensity_le_finite restrictionFinite
    leftMeasurable rightMeasurable
  intro set setMeasurable
  rw [measure.withDensity_restrict left (finite.measurable index),
    measure.withDensity_restrict right (finite.measurable index),
    (measure.withDensity left).restrict_apply (finite.sets index) setMeasurable,
    (measure.withDensity right).restrict_apply (finite.sets index) setMeasurable]
  exact included (Set.inter set (finite.sets index))
    (space.inter setMeasurable (finite.measurable index))

/-- Under a sigma-finite reference measure, density-weighted measures are
ordered on measurable sets if and only if their measurable densities are ordered
almost everywhere. -/
public theorem withDensity_le_iff_ae_le {left right : alpha → ENNReal}
    (finite : SigmaFinite measure)
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right) :
    (∀ set, space.Measurable set →
      ENNReal.le ((measure.withDensity left) set) ((measure.withDensity right) set)) ↔
      measure.AE (fun value => ENNReal.le (left value) (right value)) :=
  ⟨ae_le_of_withDensity_le finite leftMeasurable rightMeasurable,
    fun included set _ => withDensity_mono_ae included set⟩

end Problib.Measure.Measure
