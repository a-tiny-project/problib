module

public import Problib.Measure.Additive.Finite
public import Problib.Real.Nonnegative.Finite

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u v

public section

variable {alpha : Type u} {space : Space alpha}

/-- Certificate that a measure on an arbitrary measurable space has finite, nonzero total mass.
Distinct from rewriting normalization in `Foundations.Normalization`. -/
structure IsNormalizable (measure : Measure space) : Prop where
  finite : IsFinite measure
  nonzero : measure Set.univ ≠ ENNReal.zero

/-- The zero measure is not normalizable because its total mass is zero. -/
theorem zero_not_normalizable (space : Space alpha) :
    ¬IsNormalizable (zero space) :=
  fun defined => defined.nonzero (zero_apply Set.univ)

/-- A measure with infinite total mass is not normalizable. -/
theorem infinite_not_normalizable {measure : Measure space}
    (infinite : measure Set.univ = ENNReal.top) : ¬IsNormalizable measure :=
  fun defined => ENNReal.finite_iff_ne_top.mp defined.finite.univ_finite infinite

/-- A measure whose total mass is a finite nonzero value is normalizable. -/
theorem IsNormalizable.of_finite_mass {measure : Measure space} {mass : NNReal}
    (total : measure Set.univ = ENNReal.finite mass) (nonzero : mass ≠ NNReal.zero) :
    IsNormalizable measure where
  finite := ⟨by rw [total]; exact True.intro⟩
  nonzero := by
    rw [total]
    intro vanished
    exact nonzero (ENNReal.finite_injective vanished)

/-- Construct a probability measure by scaling a normalizable measure by the reciprocal of its total mass. -/
noncomputable def normalize (measure : Measure space)
    (defined : IsNormalizable measure) : Measure space :=
  let mass := Classical.choose (ENNReal.exists_finite_of_finite defined.finite.univ_finite)
  smul (ENNReal.finite (NNReal.div NNReal.one mass)) measure

/-- Normalization formula when the total mass is known as an explicit finite value. -/
theorem normalize_eq_of_total_eq (measure : Measure space)
    (defined : IsNormalizable measure) {mass : NNReal}
    (total : measure Set.univ = ENNReal.finite mass) :
    normalize measure defined = smul (ENNReal.finite (NNReal.div NNReal.one mass)) measure := by
  have selected := Classical.choose_spec
    (ENNReal.exists_finite_of_finite defined.finite.univ_finite)
  have same := ENNReal.finite_injective (selected.symm.trans total)
  unfold normalize
  rw [same]

/-- Equal measures have equal normalizations, whatever certificate each carries. -/
theorem normalize_congr {left right : Measure space} (equal : left = right)
    (leftDefined : IsNormalizable left) (rightDefined : IsNormalizable right) :
    normalize left leftDefined = normalize right rightDefined := by
  cases equal
  rfl

/-- Normalization of any normalizable measure produces an exact probability measure with total mass one. -/
theorem normalize_isProbability (measure : Measure space)
    (defined : IsNormalizable measure) : IsProbability (normalize measure defined) := by
  rcases ENNReal.exists_finite_of_finite defined.finite.univ_finite with ⟨mass, total⟩
  have nonzero : mass ≠ NNReal.zero := by
    intro zero
    exact defined.nonzero (total.trans (congrArg ENNReal.finite zero))
  constructor
  rw [normalize_eq_of_total_eq measure defined total,
    smul_apply_measurable _ _ space.univ, total]
  change ENNReal.finite (NNReal.mul (NNReal.div NNReal.one mass) mass) = ENNReal.one
  rw [NNReal.div_mul_cancel NNReal.one nonzero]
  rfl

/-- Exact reconstruction: scaling the normalized probability measure by the original total mass recovers the original measure. -/
theorem smul_normalize (measure : Measure space) (defined : IsNormalizable measure) :
    smul (measure Set.univ) (normalize measure defined) = measure := by
  rcases ENNReal.exists_finite_of_finite defined.finite.univ_finite with ⟨mass, total⟩
  have nonzero : mass ≠ NNReal.zero := by
    intro zero
    exact defined.nonzero (total.trans (congrArg ENNReal.finite zero))
  rw [normalize_eq_of_total_eq measure defined total, total, smul_smul]
  have cancel : ENNReal.mul (ENNReal.finite mass)
      (ENNReal.finite (NNReal.div NNReal.one mass)) = ENNReal.one :=
    congrArg ENNReal.finite (NNReal.mul_div_cancel NNReal.one nonzero)
  rw [cancel, one_smul]

/-- Uniqueness of reconstruction: any measure whose scaling by the original mass reconstructs the original measure equals `normalize`. -/
theorem normalize_eq_of_smul_eq (measure : Measure space) (defined : IsNormalizable measure)
    (candidate : Measure space) (reconstruct : smul (measure Set.univ) candidate = measure) :
    normalize measure defined = candidate := by
  rcases ENNReal.exists_finite_of_finite defined.finite.univ_finite with ⟨mass, total⟩
  have nonzero : mass ≠ NNReal.zero := by
    intro zero
    exact defined.nonzero (total.trans (congrArg ENNReal.finite zero))
  rw [normalize_eq_of_total_eq measure defined total, ← reconstruct, total, smul_smul]
  have cancel : ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one mass))
      (ENNReal.finite mass) = ENNReal.one :=
    congrArg ENNReal.finite (NNReal.div_mul_cancel NNReal.one nonzero)
  rw [cancel, one_smul]

/-- Every probability measure is normalizable, with total mass one. -/
theorem IsProbability.to_normalizable {measure : Measure space}
    (probability : IsProbability measure) : IsNormalizable measure where
  finite := probability.to_finite
  nonzero := by rw [probability.univ_eq_one]; exact ENNReal.one_ne_zero

/-- Normalization of an existing probability measure is the identity. -/
theorem normalize_eq_self {measure : Measure space} (probability : IsProbability measure) :
    normalize measure probability.to_normalizable = measure := by
  apply normalize_eq_of_smul_eq
  rw [probability.univ_eq_one, one_smul]

/-- Pushforward along a measurable map preserves normalizability. -/
theorem IsNormalizable.map {beta : Type v} {target : Space beta}
    {measure : Measure space} (defined : IsNormalizable measure)
    (function : alpha → beta) (measurable : MeasurableMap space target function) :
    IsNormalizable (measure.map function measurable) where
  finite := defined.finite.map function measurable
  nonzero := by
    rw [Measure.map_apply _ _ _ target.univ, Set.preimage_univ]
    exact defined.nonzero

/-- Normalization commutes with measurable pushforward. -/
theorem normalize_map {beta : Type v} {target : Space beta}
    (measure : Measure space) (defined : IsNormalizable measure)
    (function : alpha → beta) (measurable : MeasurableMap space target function) :
    normalize (measure.map function measurable) (defined.map function measurable) =
      (normalize measure defined).map function measurable := by
  apply normalize_eq_of_smul_eq
  rw [Measure.map_apply _ _ _ target.univ, Set.preimage_univ,
    ← map_smul, smul_normalize]

/-- Exact criterion: a measure is normalizable iff it can be scaled by some factor in `ENNReal` to a probability measure. -/
theorem isNormalizable_iff_probability_scaling (measure : Measure space) :
    IsNormalizable measure ↔ ∃ factor : ENNReal, IsProbability (smul factor measure) := by
  constructor
  · intro defined
    refine ⟨ENNReal.finite (NNReal.div NNReal.one
      (Classical.choose (ENNReal.exists_finite_of_finite defined.finite.univ_finite))), ?_⟩
    exact normalize_isProbability measure defined
  · rintro ⟨factor, probability⟩
    have total := probability.univ_eq_one
    rw [smul_apply_measurable _ _ space.univ] at total
    have nonzero : measure Set.univ ≠ ENNReal.zero := by
      intro zero
      rw [zero, ENNReal.mul_zero] at total
      exact ENNReal.one_ne_zero total.symm
    refine ⟨⟨ENNReal.finite_iff_ne_top.mpr ?_⟩, nonzero⟩
    intro infinite
    rw [infinite] at total
    classical
    by_cases zero : factor = ENNReal.zero
    · rw [zero, ENNReal.zero_mul] at total
      exact ENNReal.one_ne_zero total.symm
    · rw [ENNReal.mul_top_of_ne_zero zero] at total
      exact ENNReal.top_ne_finite NNReal.one total

end

end Problib.Measure.Measure
