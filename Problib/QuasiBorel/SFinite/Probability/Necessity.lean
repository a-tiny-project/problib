import Problib.QuasiBorel.SFinite.Probability.Normalized
import Problib.QuasiBorel.Initial

/-!
# Necessity witnesses for normalized s-finite laws

This module constructs two necessity counterexamples:
1. The normalized empty quasi-Borel space has no points, refuting normalized
   laws on initial empty carriers.
2. A concrete presentation with infinite raw source mass whose interpreted
   measure has total mass one, proving that presentations of normalized laws
   do not require normalized or finite raw source measures.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)
open Problib.Real (ENNReal)

universe u

/-- The normalized law space on the initial empty quasi-Borel space is empty. -/
theorem normalized_initial_empty :
    ¬Nonempty (Normalized.Law (Space.initial.{0, u} realSource)) := by
  rintro ⟨law⟩
  rcases law.property.nonempty with ⟨point⟩
  exact point.elim

/-- Construction of a presentation with infinite raw source mass that presents a probability law. -/
theorem normalized_law_with_infinite_source :
    ∃ presentation : Presentation (Space.terminal realSource),
      presentation.sourceMeasure Set.univ = ENNReal.top ∧
        Measure.IsProbability presentation.toMeasure := by
  classical
  let space := Space.terminal realSource
  let seed := Problib.Real.Construction.Dedekind.zero
  let branches : Nat → Carrier → (withFailure space).Carrier :=
    fun index _ => if index = 0 then Sum.inr () else Sum.inl ()
  let accepted := RandomFamily.join_random (space := withFailure space)
    (fun index => (withFailure space).constant (if index = 0 then Sum.inr () else Sum.inl ()))
  let sourceMeasure := Measure.sum (fun index => Measure.dirac borel (RandomFamily.select index seed))
  let presentation : Presentation space := {
    random := RandomFamily.join branches
    accepted := accepted
    sourceMeasure := sourceMeasure
    sfinite := {
      components := fun index => Measure.dirac borel (RandomFamily.select index seed)
      finite := fun index => Measure.IsFinite.dirac borel (RandomFamily.select index seed)
      sum_eq := rfl
    }
  }
  refine ⟨presentation, ?_, ?_⟩
  · change sourceMeasure Set.univ = ENNReal.top
    rw [Measure.sum_apply _ borel.univ]
    simp only [Measure.dirac_apply_univ]
    exact ENNReal.tsum_const_of_ne_zero ENNReal.one_ne_zero
  · let embedding := Space.inrEmbedding (Space.terminal realSource) space
    let success := Set.preimage presentation.random (Set.image embedding.function Set.univ)
    have measurable : borel.Measurable success :=
      Space.random_measurable accepted (embedding.image_measurable Set.univ space.toMeasurable.univ)
    have selected (index : Nat) : success (RandomFamily.select index seed) ↔ index = 0 := by
      change (∃ point, True ∧ Sum.inr point = RandomFamily.join branches (RandomFamily.select index seed)) ↔ _
      rw [RandomFamily.join_select]
      change (∃ point, True ∧ Sum.inr point = if index = 0 then Sum.inr () else Sum.inl ()) ↔ _
      by_cases equal : index = 0
      · rw [if_pos equal]
        exact ⟨fun _ => equal, fun _ => ⟨(), True.intro, rfl⟩⟩
      · rw [if_neg equal]
        constructor
        · rintro ⟨point, member, impossible⟩
          cases impossible
        · intro impossible
          exact (equal impossible).elim
    constructor
    change presentation.toMeasure Set.univ = ENNReal.one
    rw [Presentation.toMeasure, Measure.comap_apply _ _ (by exact space.toMeasurable.univ),
      Measure.map_apply _ _ (Space.random_measurable accepted)
        (by exact embedding.image_measurable Set.univ space.toMeasurable.univ)]
    change sourceMeasure success = ENNReal.one
    rw [Measure.sum_apply _ @measurable,
      ENNReal.tsum_eq_of_at_most_one_nonzero _ 0 (by
        intro index different
        exact Measure.dirac_apply_of_not_mem _ _ @measurable
          (fun member => different ((selected index).mp member)))]
    exact Measure.dirac_apply_of_mem _ _ @measurable ((selected 0).mpr rfl)

end Problib.QuasiBorel.SFinite
