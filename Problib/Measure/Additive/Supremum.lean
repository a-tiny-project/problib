module

public import Problib.Measure.Additive.Sum
public import Problib.Real.Series.Convergence

set_option autoImplicit false

/-! Increasing chains of measures have a pointwise supremum on measurable sets. -/

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- The measure obtained by taking the increasing limit of a countable chain. -/
@[expose] public noncomputable def iSupIncreasing
    (measures : Nat → Measure space)
    (monotone : ∀ index set, space.Measurable set →
      ENNReal.le (measures index set) (measures (index + 1) set)) :
    Measure space where
  content := fun set measurable =>
    ENNReal.iSup (fun index => (measures index).content set measurable)
  empty := by
    have empty : ∀ index, (measures index).content Set.empty space.empty = ENNReal.zero :=
      fun index => (measures index).empty
    simp only [empty, ENNReal.iSup_const]
  content_iUnion_disjoint := by
    intro sets measurable disjoint
    have increasing : ∀ index term,
        ENNReal.le ((measures index).content (sets term) (measurable term))
          ((measures (index + 1)).content (sets term) (measurable term)) := by
      intro index term
      simpa only [← (measures index).apply_measurable (measurable term),
        ← (measures (index + 1)).apply_measurable (measurable term)] using
        monotone index (sets term) (measurable term)
    rw [ENNReal.tsum_iSup (fun index term =>
      (measures index).content (sets term) (measurable term)) increasing]
    apply congrArg ENNReal.iSup
    funext index
    exact (measures index).content_iUnion_disjoint sets measurable disjoint

/-- On a measurable region the limit is the supremum of the chain's masses. -/
public theorem iSupIncreasing_apply_measurable
    (measures : Nat → Measure space)
    (monotone : ∀ index set, space.Measurable set →
      ENNReal.le (measures index set) (measures (index + 1) set))
    {set : Set alpha} (measurable : space.Measurable set) :
    iSupIncreasing measures monotone set =
      ENNReal.iSup (fun index => measures index set) := by
  rw [(iSupIncreasing measures monotone).apply_measurable measurable]
  apply congrArg ENNReal.iSup
  funext index
  exact ((measures index).apply_measurable measurable).symm

end Problib.Measure.Measure
