module

public import Problib.Measure.Decomposition.ZeroInfinity
public import Problib.Measure.Necessity.Density

set_option autoImplicit false

namespace Problib.Measure.Necessity.ZeroInfinity

open Problib.Real

/-- A countable sum of unit Dirac measures on the one-point space makes the
ambient space a zero-infinity set. -/
public theorem reference_univ_zero_infinity :
    Measure.IsZeroInfinitySet Density.reference Set.univ := by
  refine ⟨True.intro, ?_⟩
  intro subset measurable _
  rw [Density.reference_eq_top_smul,
    Measure.smul_apply_measurable _ _ measurable]
  classical
  by_cases zero : (Measure.dirac (Space.discrete Unit) ()) subset = ENNReal.zero
  · exact Or.inl (zero ▸ ENNReal.mul_zero ENNReal.top)
  · exact Or.inr (ENNReal.top_mul_of_ne_zero zero)

/-- The one-point infinite Dirac sum witnesses that an s-finite measure can
admit a non-null zero-infinity set spanning the space. -/
public theorem s_finite_zero_infinity_need_not_be_null :
    Nonempty (Measure.SFinite Density.reference) ∧
      ¬Nonempty (Measure.SigmaFinite Density.reference) ∧
      Measure.IsZeroInfinitySet Density.reference Set.univ ∧
      ¬Density.reference.NullSet Set.univ := by
  refine ⟨⟨Density.reference_sFinite⟩, Density.reference_not_sigmaFinite,
    reference_univ_zero_infinity, ?_⟩
  intro null
  change Density.reference Set.univ = ENNReal.zero at null
  rw [Density.reference_univ] at null
  exact ENNReal.top_ne_finite NNReal.zero null

/-- Every greatest zero-infinity set for the one-point infinite Dirac sum has
infinite mass. -/
public theorem reference_top_mass (top : Measure.TopZeroInfinitySet Density.reference) :
    Density.reference top.set = ENNReal.top := by
  have nonnull : ¬Density.reference.NullSet top.set := by
    intro null
    exact Density.reference_not_sigmaFinite
      ((top.null_iff_sigmaFinite Density.reference_sFinite).mp null)
  exact (top.zero_infinity.subsets_zero_or_top top.zero_infinity.measurable
    (fun {_} member => member)).resolve_left nonnull

/-- The restriction of the one-point infinite Dirac sum to the complement of
any greatest zero-infinity set vanishes. -/
public theorem reference_top_complement_eq_zero
    (top : Measure.TopZeroInfinitySet Density.reference) :
    Density.reference.restrict (Set.complement top.set) =
      Measure.zero (Space.discrete Unit) := by
  apply Density.reference.restrict_eq_zero_of_null
  have null := top.greatest reference_univ_zero_infinity
  have same : Set.difference Set.univ top.set = Set.complement top.set := by
    apply Set.ext
    intro value
    exact ⟨fun member => member.2, fun member => ⟨True.intro, member⟩⟩
  rw [same] at null
  exact null

/-- The unit Dirac measure is not zero-infinity absolutely continuous with
respect to the one-point infinite Dirac sum reference measure. -/
public theorem dirac_not_zeroInfinityAbsolutelyContinuous :
    ¬Measure.ZeroInfinityAbsolutelyContinuous (Measure.dirac (Space.discrete Unit) ()) Necessity.Density.reference := by
  intro continuous
  have zeroInfinity := continuous.preserves_zero_infinity Necessity.ZeroInfinity.reference_univ_zero_infinity
  have dichotomy := zeroInfinity.subsets_zero_or_top (Space.discrete Unit).univ
    (show Set.Subset Set.univ Set.univ from fun {_} member => member)
  rw [Measure.dirac_apply_univ] at dichotomy
  rcases dichotomy with zero | infinite
  · exact ENNReal.one_ne_zero zero
  · exact ENNReal.finite_ne_top NNReal.one infinite

/-- Constants one and two under the infinite-atom reference measure on the
one-point space are almost-everywhere-infinity equal but not almost-everywhere
equal. -/
public theorem reference_aeInfinityEq_not_aeEq (top : Measure.TopZeroInfinitySet Density.reference) :
    top.AEInfinityEq (fun _ => ENNReal.one) (fun _ => Density.two) ∧
    ¬Density.reference.AEEq (fun _ => ENNReal.one) (fun _ => Density.two) :=
  ⟨(Measure.withDensity_eq_iff_aeInfinityEq Density.reference_sFinite top
      (ENNRealMeasurable.constant _ _) (ENNRealMeasurable.constant _ _)).mp
      Density.same_weighted_measure,
    Density.densities_not_ae_equal⟩

end Problib.Measure.Necessity.ZeroInfinity
