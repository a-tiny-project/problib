module

public import Problib.QuasiBorel.SFinite.Presentation

set_option autoImplicit false

/-!
# Necessity counterexamples for s-finite quasi-Borel spaces

This module proves structural counterexamples and necessity witnesses.
Total generators from the nonempty real line require an inhabited target carrier,
preventing total real presentations of the zero measure on empty spaces.
Distinct presentations with zero versus Dirac source mass interpret as the
same measure, demonstrating that presentation equality is strictly finer than
measure equality.
-/
namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure.Real (Carrier borel)
open Problib.Measure hiding Space
open Problib.Real (ENNReal)

universe u

/-- Proves that any total random map from the real line witnesses an inhabited target. -/
theorem total_generator_requires_inhabitant {α : Type u} (random : Carrier → α) :
    Nonempty α :=
  ⟨random Problib.Real.Construction.Dedekind.zero⟩

/-- Refutes the existence of any total random map from the real line into the empty type. -/
theorem no_total_generator_empty : ¬Nonempty (Carrier → PEmpty.{u + 1}) := by
  rintro ⟨random⟩
  exact (random Problib.Real.Construction.Dedekind.zero).elim

/-- Proves that the empty space admits a zero measure without admitting any total generator from the real line. -/
theorem zero_measure_without_total_generator :
    Nonempty (Problib.Measure.Measure
      (Problib.Measure.Space.discrete PEmpty.{u + 1})) ∧
      ¬Nonempty (Carrier → PEmpty.{u + 1}) :=
  ⟨⟨Problib.Measure.Measure.zero _⟩, no_total_generator_empty⟩

/-- Constructs two distinct presentations that interpret as the same underlying measure. -/
theorem distinct_presentations_same_measure (space : Space realSource) :
    ∃ left right : Presentation space,
      left ≠ right ∧ left.toMeasure = right.toMeasure := by
  let point := Problib.Real.Construction.Dedekind.zero
  let left := Presentation.failed space (Measure.zero borel) (Measure.SFinite.zero borel)
  let right := Presentation.failed space (Measure.dirac borel point)
    (Measure.SFinite.ofFinite (Measure.IsFinite.dirac borel point))
  refine ⟨left, right, ?_, ?_⟩
  · intro equal
    have measures := congrArg Presentation.sourceMeasure equal
    have total := congrArg (fun measure : Measure borel => measure Set.univ) measures
    change Measure.zero borel Set.univ = Measure.dirac borel point Set.univ at total
    rw [Measure.zero_apply, Measure.dirac_apply_univ] at total
    exact ENNReal.one_ne_zero total.symm
  · exact (Presentation.failed_toMeasure space _ _).trans
      (Presentation.failed_toMeasure space _ _).symm

end

end Problib.QuasiBorel.SFinite
