module

public import Problib.Measure.StandardBorel.Basic
public import Problib.Measure.Additive.Finite
public import Problib.Measure.AlmostEverywhere.Basic
import Problib.Measure.Additive.Comap
import Problib.Measure.Real.Uniqueness
import Problib.Measure.Extended.Unit.Basis

set_option autoImplicit false

namespace Problib.Measure.StandardBorel

open Problib.Real
open Problib.Real.Construction
open Problib.Measure.Real

universe u v

/-- Two arbitrary measure families into a standard-Borel space that are
almost-everywhere finite and agree eventwise almost everywhere for each
measurable event are equal almost everywhere as whole measures on one common
full-measure set.
The parameter space and parameter measure are arbitrary, and the parameter
measure can be infinite or non-σ-finite.
Families need only be finite almost everywhere, so exceptional fibers can be
infinite.
The theorem requires no kernel structure, family measurability, normalization,
uniform mass bound, parameter σ-finiteness, or inhabitedness.
The proof forms a countable conjunction across rational initial intervals and
total mass, applying finite-measure determination and pulling whole-measure
equality back through the standard-Borel embedding into the unit interval. -/
public theorem aeEq_of_apply_aeEq
    {alpha : Type u} {beta : Type v} {source : Space alpha} {parameter : Space beta}
    {measure : Measure parameter}
    (presentation : StandardBorel source)
    (first second : beta → Measure source)
    (firstFinite : measure.AE (fun input => Measure.IsFinite (first input)))
    (secondFinite : measure.AE (fun input => Measure.IsFinite (second input)))
    (evaluations : ∀ set, source.Measurable set → measure.AEEq
      (fun input => first input set) (fun input => second input set)) :
    measure.AEEq (fun input => first input) (fun input => second input) := by
  let embedding := presentation.embedding
  have events (index : Nat) := evaluations _
    (embedding.measurable (unitInitial_measurable (unitRationalBasis index)))
  have together : measure.AE (fun input => ∀ index,
      first input (Set.preimage embedding.function (unitInitial (unitRationalBasis index))) =
        second input (Set.preimage embedding.function (unitInitial (unitRationalBasis index)))) :=
    Measure.ae_all_iff.mpr events
  have totals := evaluations Set.univ source.univ
  apply (((together.and totals).and firstFinite).and secondFinite).mono
  intro input valid
  rcases valid with ⟨⟨⟨eventsAgree, totalAgree⟩, leftFinite⟩, rightFinite⟩
  have mapped : (first input).map embedding.function embedding.measurable =
      (second input).map embedding.function embedding.measurable := by
    apply finite_measure_ext_right_dense (leftFinite.map embedding.function embedding.measurable)
      (rightFinite.map embedding.function embedding.measurable) unitRationalBasis
    · intro point next less
      rcases exists_unitRationalBasis_between less with ⟨index, above, below⟩
      exact ⟨index, above, below.1⟩
    · rw [Measure.map_apply _ _ _ unitBorel.univ, Measure.map_apply _ _ _ unitBorel.univ,
        Set.preimage_univ]
      exact totalAgree
    · intro index
      rw [Measure.map_apply _ _ _ (unitInitial_measurable _),
        Measure.map_apply _ _ _ (unitInitial_measurable _)]
      exact eventsAgree index
  have pulled := congrArg (fun measure => measure.comap embedding) mapped
  simpa only [Measure.comap_map] using pulled

end Problib.Measure.StandardBorel
