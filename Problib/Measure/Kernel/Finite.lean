module

public import Problib.Measure.Kernel.Piecewise
public import Problib.Real.Series.Basis

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u v
variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Construct an explicit s-finite decomposition for any measurable kernel with
finite individual fiber measures. -/
public noncomputable def IsSFinite.ofFiniteFibers {kernel : Kernel source target}
    (finite : ∀ input, Measure.IsFinite (kernel input)) : Kernel.IsSFinite kernel := by
  classical
  let cover := fun index input =>
    ENNReal.le (kernel input Set.univ) (ENNReal.rationalBasis index)
  have coverMeasurable : ∀ index, source.Measurable (cover index) :=
    fun index => (kernel.measurable target.univ).iic (ENNReal.rationalBasis index)
  have covers : Set.iUnion cover = Set.univ := by
    apply Set.ext
    intro input
    constructor
    · intro _
      exact True.intro
    · intro _
      have below : ENNReal.lt (kernel input Set.univ) ENNReal.top :=
        ⟨ENNReal.le_top _, fun reverse =>
          (ENNReal.finite_iff_ne_top.mp (finite input).univ_finite)
            (ENNReal.top_le_iff.mp reverse)⟩
      rcases ENNReal.exists_rationalBasis_between below with ⟨index, included, _⟩
      exact ⟨index, included.1⟩
  let pieces := Set.disjointed cover
  have piecesMeasurable : ∀ index, source.Measurable (pieces index) :=
    source.disjointed_measurable coverMeasurable
  let components := fun index => Kernel.piecewise (pieces index) (piecesMeasurable index)
    kernel (Kernel.zero source target)
  refine { components := components, finite := ?_, sum_eq := ?_ }
  · intro index
    refine ⟨⟨ENNReal.rationalBasis index, ENNReal.rationalBasis_finite index, ?_⟩⟩
    intro input
    by_cases member : pieces index input
    · change ENNReal.le ((if pieces index input then kernel input else Measure.zero target) Set.univ) _
      rw [if_pos member]
      exact (Set.disjointed_subset cover index member)
    · change ENNReal.le ((if pieces index input then kernel input else Measure.zero target) Set.univ) _
      rw [if_neg member, Measure.zero_apply]
      exact ENNReal.zero_le _
  · apply Kernel.ext
    intro input
    apply Measure.ext
    intro set setMeasurable
    rw [Kernel.sum_apply, Measure.sum_apply _ setMeasurable]
    have existsIndex : ∃ index, pieces index input := by
      change Set.iUnion (Set.disjointed cover) input
      rw [Set.iUnion_disjointed, covers]
      exact True.intro
    rcases existsIndex with ⟨selected, present⟩
    have equal : (fun index => components index input set) =
        ENNReal.single selected (kernel input set) := by
      funext index
      by_cases same : index = selected
      · subst index
        change (if pieces selected input then kernel input else Measure.zero target) set = _
        rw [if_pos present]
        simp [ENNReal.single]
      · have absent : ¬pieces index input := fun member =>
          Set.disjointed_pairwise cover index selected same member present
        change (if pieces index input then kernel input else Measure.zero target) set = _
        rw [if_neg absent, Measure.zero_apply]
        simp only [ENNReal.single, if_neg same]
    rw [equal, ENNReal.tsum_single]

end Problib.Measure.Kernel
