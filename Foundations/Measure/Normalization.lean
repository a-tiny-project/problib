module

public import Foundations.Measure.Additive.Finite
public import Foundations.Real.Nonnegative.Finite

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

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
  fun defined => ENNReal.finiteIffNeTop.mp defined.finite.univFinite infinite

/-- Construct a probability measure by scaling a normalizable measure by the reciprocal of its total mass. -/
noncomputable def normalize (measure : Measure space)
    (defined : IsNormalizable measure) : Measure space :=
  let mass := Classical.choose (ENNReal.existsFiniteOfFinite defined.finite.univFinite)
  smul (ENNReal.finite (NNReal.div NNReal.one mass)) measure

/-- Normalization formula when the total mass is known as an explicit finite value. -/
theorem normalize_eq_of_total_eq (measure : Measure space)
    (defined : IsNormalizable measure) {mass : NNReal}
    (total : measure Set.univ = ENNReal.finite mass) :
    normalize measure defined = smul (ENNReal.finite (NNReal.div NNReal.one mass)) measure := by
  have selected := Classical.choose_spec
    (ENNReal.existsFiniteOfFinite defined.finite.univFinite)
  have same := ENNReal.finiteInjective (selected.symm.trans total)
  unfold normalize
  rw [same]

/-- Normalization of any normalizable measure produces an exact probability measure with total mass one. -/
theorem normalize_isProbability (measure : Measure space)
    (defined : IsNormalizable measure) : IsProbability (normalize measure defined) := by
  rcases ENNReal.existsFiniteOfFinite defined.finite.univFinite with ⟨mass, total⟩
  have nonzero : mass ≠ NNReal.zero := by
    intro zero
    exact defined.nonzero (total.trans (congrArg ENNReal.finite zero))
  constructor
  rw [normalize_eq_of_total_eq measure defined total,
    smul_apply_measurable _ _ space.univ, total]
  change ENNReal.finite (NNReal.mul (NNReal.div NNReal.one mass) mass) = ENNReal.one
  rw [NNReal.divMulCancel NNReal.one nonzero]
  rfl

/-- Exact reconstruction: scaling the normalized probability measure by the original total mass recovers the original measure. -/
theorem smul_normalize (measure : Measure space) (defined : IsNormalizable measure) :
    smul (measure Set.univ) (normalize measure defined) = measure := by
  rcases ENNReal.existsFiniteOfFinite defined.finite.univFinite with ⟨mass, total⟩
  have nonzero : mass ≠ NNReal.zero := by
    intro zero
    exact defined.nonzero (total.trans (congrArg ENNReal.finite zero))
  rw [normalize_eq_of_total_eq measure defined total, total, smul_smul]
  have cancel : ENNReal.mul (ENNReal.finite mass)
      (ENNReal.finite (NNReal.div NNReal.one mass)) = ENNReal.one :=
    congrArg ENNReal.finite (NNReal.mulDivCancel NNReal.one nonzero)
  rw [cancel, one_smul]

/-- Uniqueness of reconstruction: any measure whose scaling by the original mass reconstructs the original measure equals `normalize`. -/
theorem normalize_eq_of_smul_eq (measure : Measure space) (defined : IsNormalizable measure)
    (candidate : Measure space) (reconstruct : smul (measure Set.univ) candidate = measure) :
    normalize measure defined = candidate := by
  rcases ENNReal.existsFiniteOfFinite defined.finite.univFinite with ⟨mass, total⟩
  have nonzero : mass ≠ NNReal.zero := by
    intro zero
    exact defined.nonzero (total.trans (congrArg ENNReal.finite zero))
  rw [normalize_eq_of_total_eq measure defined total, ← reconstruct, total, smul_smul]
  have cancel : ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one mass))
      (ENNReal.finite mass) = ENNReal.one :=
    congrArg ENNReal.finite (NNReal.divMulCancel NNReal.one nonzero)
  rw [cancel, one_smul]

/-- Every probability measure is normalizable, with total mass one. -/
theorem IsProbability.toNormalizable {measure : Measure space}
    (probability : IsProbability measure) : IsNormalizable measure where
  finite := probability.toFinite
  nonzero := by rw [probability.univ_eq_one]; exact ENNReal.oneNeZero

/-- Normalization of an existing probability measure is the identity. -/
theorem normalize_eq_self {measure : Measure space} (probability : IsProbability measure) :
    normalize measure probability.toNormalizable = measure := by
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
      (Classical.choose (ENNReal.existsFiniteOfFinite defined.finite.univFinite))), ?_⟩
    exact normalize_isProbability measure defined
  · rintro ⟨factor, probability⟩
    have total := probability.univ_eq_one
    rw [smul_apply_measurable _ _ space.univ] at total
    have nonzero : measure Set.univ ≠ ENNReal.zero := by
      intro zero
      rw [zero, ENNReal.mulZero] at total
      exact ENNReal.oneNeZero total.symm
    refine ⟨⟨ENNReal.finiteIffNeTop.mpr ?_⟩, nonzero⟩
    intro infinite
    rw [infinite] at total
    classical
    by_cases zero : factor = ENNReal.zero
    · rw [zero, ENNReal.zeroMul] at total
      exact ENNReal.oneNeZero total.symm
    · rw [ENNReal.mulTopOfNeZero zero] at total
      exact ENNReal.topNeFinite NNReal.one total

end

end Foundations.Measure.Measure
