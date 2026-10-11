module

public import Problib.Measure.Additive.Counting
public import Problib.Measure.Integral.Density.Basic
public import Problib.Measure.Integral.Lebesgue.Algebra
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Analysis.Real.SignedSeries
public import Problib.Analysis.Real.Sequence

/-! Laws on the naturals from a mass function.

A law on `ℕ` that gives each count `k` the mass `mass k` is the counting
measure with density `mass` (`ofMass`). That density is the law's density
against the counting reference by definition, so a count block's density
certificate needs no proof beyond its own `ofMass`. The law of a single count is
its mass (`ofMass_singleton`), the whole law is the sum of the masses
(`ofMass_univ`), and two laws on `ℕ` that agree on every count are equal
(`ext_singleton`). Masses that are nonnegative reals summing to one, as a real
series, give a probability law (`ofMass_isProbability`), through the sum of
their extended reals (`tsum_ofReal`).
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Count

open Problib.Real Problib.Measure
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real (ConvergesTo limit_le_of_eventually_le abs_lt)
open Problib.Analysis.Real.SignedSeries (partialSum partialSum_monotone partialSum_nonnegative)

noncomputable section

/-- The law on `ℕ` with mass `mass k` at each count `k`. -/
@[expose] public def ofMass (mass : Nat → NNReal) : Measure (Space.discrete Nat) :=
  Measure.counting.withDensity fun count => ENNReal.finite (mass count)

/-- Every function on the naturals is measurable. -/
public theorem mass_measurable (mass : Nat → ENNReal) : ENNRealMeasurable (Space.discrete Nat) mass :=
  ENNRealMeasurable.of_measurableMap (MeasurableMap.from_discrete _ _)

/-- Counting on the naturals is the sum of the unit masses at each count. -/
private theorem counting_eq_sum :
    Measure.counting = Measure.sum fun index => Measure.dirac (Space.discrete Nat) index := by
  apply Measure.ext_of_atoms id (fun _ _ equal => equal) (fun _ => Space.discrete_measurable _)
  intro count
  change Measure.counting (fun value => value = count) =
    Measure.sum (fun index => Measure.dirac (Space.discrete Nat) index) (fun value => value = count)
  rw [Measure.counting_singleton, Measure.sum_apply _ (Space.discrete_measurable _),
    ENNReal.tsum_eq_of_at_most_one_nonzero
      (fun index => Measure.dirac (Space.discrete Nat) index (fun value => value = count)) count
      fun other different => Measure.dirac_apply_of_not_mem _ _ (Space.discrete_measurable _)
        different]
  exact (Measure.dirac_apply_of_mem (Space.discrete Nat) count (set := fun value => value = count)
    (Space.discrete_measurable _) rfl).symm

/-- Integrating against counting sums over the naturals. -/
public theorem lintegral_counting (function : Nat → ENNReal) :
    lintegral Measure.counting function = ENNReal.tsum function := by
  rw [counting_eq_sum, lintegral_sum]
  exact ENNReal.tsum_congr fun index => lintegral_dirac _ index (mass_measurable function)

/-- A law on `ℕ` from masses gives each count its mass. -/
public theorem ofMass_singleton (mass : Nat → NNReal) (count : Nat) :
    ofMass mass (fun value => value = count) = ENNReal.finite (mass count) := by
  rw [ofMass, Measure.withDensity_apply _ _ (Space.discrete_measurable _),
    ← lintegral_indicator _ _ (Space.discrete_measurable _), lintegral_counting]
  refine (ENNReal.tsum_eq_of_at_most_one_nonzero
    (ennrealIndicator (fun value => value = count) fun count => ENNReal.finite (mass count)) count
    fun other different =>
    ennrealIndicator_of_not_mem different).trans ?_
  exact ennrealIndicator_of_mem rfl

/-- The total of a law from masses is the sum of the masses. -/
public theorem ofMass_univ (mass : Nat → NNReal) :
    ofMass mass Set.univ = ENNReal.tsum fun count => ENNReal.finite (mass count) := by
  rw [ofMass, Measure.withDensity_apply _ _ (Space.univ _), Measure.restrict_univ, lintegral_counting]

/-- Laws on `ℕ` agreeing on every count are equal. -/
public theorem ext_singleton {left right : Measure (Space.discrete Nat)}
    (same : ∀ count, left (fun value => value = count) = right (fun value => value = count)) :
    left = right :=
  Measure.ext_of_atoms id (fun _ _ equal => equal) (fun _ => Space.discrete_measurable _) same

/-- A nonnegative real series converging to `total` sums, as extended reals, to
`total`. -/
public theorem tsum_ofReal {values : Nat → selection.Carrier} (nonnegative : ∀ count, le zero (values count))
    {total : selection.Carrier} (converges : ConvergesTo (partialSum values) total) :
    ENNReal.tsum (fun count => ENNReal.ofReal (values count)) = ENNReal.ofReal total := by
  have partials : ∀ count, ENNReal.partialSum (fun count => ENNReal.ofReal (values count)) count =
      ENNReal.ofReal (partialSum values count) := by
    intro count
    induction count with
    | zero => exact ENNReal.ofReal_zero.symm
    | succ count induction =>
        show ENNReal.add (ENNReal.partialSum _ count) _ = _
        rw [induction]
        exact (ENNReal.ofReal_add (partialSum_nonnegative nonnegative count) (nonnegative count)).symm
  have below : ∀ count, le (partialSum values count) total := by
    intro count
    apply Classical.byContradiction
    intro above
    obtain ⟨stage, close⟩ := converges _ (sub_positive_iff.mpr (lt_of_not_le above))
    have later := partialSum_monotone nonnegative (Nat.le_max_right stage count)
    have upper := add_lt_add_le (abs_lt.mp (close (max stage count) (Nat.le_max_left _ _))).2
      (le_refl total)
    rw [sub_add_cancel, sub_add_cancel] at upper
    exact lt_irrefl _ (lt_of_le_of_lt later upper)
  unfold ENNReal.tsum
  have same : ENNReal.partialSum (fun count => ENNReal.ofReal (values count)) =
      fun count => ENNReal.ofReal (partialSum values count) := funext partials
  rw [same]
  apply ENNReal.le_antisymm
  · exact ENNReal.iSup_le fun count => ENNReal.ofReal_monotone (below count)
  · rcases ENNReal.eq_top_or_exists_finite
        (ENNReal.iSup fun count => ENNReal.ofReal (partialSum values count)) with
      top | ⟨value, finite⟩
    · rw [top]
      exact ENNReal.le_top _
    · have bounded : ENNReal.Finite (ENNReal.finite value) := True.intro
      rw [finite, ENNReal.ofReal_le_iff_le_toReal bounded]
      apply limit_le_of_eventually_le converges 0
      intro count _
      have stage := ENNReal.le_iSup (fun count => ENNReal.ofReal (partialSum values count)) count
      rwa [finite, ENNReal.ofReal_le_iff_le_toReal bounded] at stage

/-- Masses that are nonnegative reals whose series converges to one give a
probability law. -/
public theorem ofMass_isProbability {values : Nat → selection.Carrier}
    (nonnegative : ∀ count, le zero (values count))
    (converges : ConvergesTo (partialSum values) one) :
    Measure.IsProbability (ofMass fun count => NNReal.ofReal (values count)) := by
  constructor
  rw [ofMass_univ]
  exact (tsum_ofReal nonnegative converges).trans ENNReal.ofReal_one

end

end Problib.Analysis.Count
