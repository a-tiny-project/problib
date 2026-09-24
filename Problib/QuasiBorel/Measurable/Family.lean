module

public import Problib.Measure.StandardBorel.Countable
public import Problib.Measure.StandardBorel.Product
public import Problib.QuasiBorel.Measurable.Basic

set_option autoImplicit false

namespace Problib.QuasiBorel.RandomFamily

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

universe u

private noncomputable def coding :
    MeasurableEmbedding
      (Problib.Measure.Space.product (Problib.Measure.Space.discrete Nat) borel) borel :=
  (StandardBorel.natural.product StandardBorel.real).embeddingReal

private noncomputable def decode : Carrier → Nat × Carrier :=
  coding.retract (0, Problib.Real.Construction.Dedekind.zero)

private theorem decode_measurable :
    MeasurableMap borel
      (Problib.Measure.Space.product (Problib.Measure.Space.discrete Nat) borel) decode :=
  coding.retract_measurable _

/-- Injects a countable branch index and real seed into the real Borel random source through standard-Borel natural-real pairing. -/
noncomputable def select (index : Nat) (seed : Carrier) : Carrier :=
  coding.function (index, seed)

/-- Selecting a fixed countable branch coordinate is a measurable map on the real Borel line. -/
theorem select_measurable (index : Nat) : MeasurableMap borel borel (select index) :=
  MeasurableMap.comp coding.measurable
    (Problib.Measure.Space.pair_measurable
      (MeasurableMap.constant borel (Problib.Measure.Space.discrete Nat) index)
      (MeasurableMap.identity borel))

/-- Joins a countable family of random elements into a single map from the real random source by decoding branch index and seed coordinates. -/
noncomputable def join {α : Type u} (branches : Nat → Carrier → α) (seed : Carrier) : α :=
  branches (decode seed).1 (decode seed).2

/-- Evaluating the joined family along the selected branch coordinate recovers that branch element. -/
theorem join_select {α : Type u} (branches : Nat → Carrier → α)
    (index : Nat) (seed : Carrier) : join branches (select index seed) = branches index seed := by
  unfold join decode select
  rw [coding.retract_forward]

/-- Countable join of accepted random elements into any quasi-Borel space remains an accepted random element. -/
theorem join_random {space : Space (Source.ofMeasurable borel)}
    {branches : Nat → Carrier → space.Carrier} (accepted : ∀ index, space.Random (branches index)) :
    space.Random (join branches) := by
  have firstMeasurable : MeasurableMap borel (Problib.Measure.Space.discrete Nat)
      (fun seed => (decode seed).1) := MeasurableMap.comp
    (Problib.Measure.Space.first_measurable (Problib.Measure.Space.discrete Nat) borel)
    decode_measurable
  have secondMeasurable : MeasurableMap borel borel (fun seed => (decode seed).2) :=
    MeasurableMap.comp
    (Problib.Measure.Space.second_measurable (Problib.Measure.Space.discrete Nat) borel)
    decode_measurable
  have partition : (Source.ofMeasurable borel).Partition (fun seed => (decode seed).1) := by
    intro index
    exact firstMeasurable (show (Problib.Measure.Space.discrete Nat).Measurable
      (fun point => point = index) from True.intro)
  exact space.piecewise partition (fun index => space.reparam secondMeasurable (accepted index))

end

end Problib.QuasiBorel.RandomFamily
