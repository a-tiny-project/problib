module

public import Problib.Measure.Null.Basic

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Every set whose outer measure is strictly below an upper bound admits a
measurable superset with outer measure strictly below the same bound. -/
public theorem exists_measurable_superset_lt (measure : Measure space)
    {set : Set alpha} {upper : ENNReal}
    (below : ENNReal.lt (measure set) upper) :
    ∃ superset : Set alpha, space.Measurable superset ∧
      Set.Subset set superset ∧ ENNReal.lt (measure superset) upper := by
  classical
  have envelope : measure set = ENNReal.infimum (fun value =>
      ∃ cover : CountableCover set,
        value = coverCost measure.extendedContent cover) :=
    OuterMeasure.ofFunction_apply measure.extendedContent
      measure.extendedContent_empty set
  rw [envelope] at below
  rcases ENNReal.exists_less_of_infimum_lt below with
    ⟨cost, ⟨cover, rfl⟩, costBelow⟩
  have measurable : ∀ index, space.Measurable (cover.sets index) := by
    intro index
    apply Classical.byContradiction
    intro notMeasurable
    have bound := ENNReal.term_le_tsum
      (fun current => measure.extendedContent (cover.sets current)) index
    unfold extendedContent at bound
    rw [dif_neg notMeasurable] at bound
    exact costBelow.2 (ENNReal.le_trans (ENNReal.le_top upper) bound)
  refine ⟨Set.iUnion cover.sets, space.iUnion measurable, cover.covers, ?_⟩
  have unionBound : ENNReal.le (measure (Set.iUnion cover.sets))
      (coverCost measure.extendedContent cover) := by
    have bound := measure.iUnion_le cover.sets
    have terms : ∀ index, measure (cover.sets index) =
        measure.extendedContent (cover.sets index) := by
      intro index
      rw [measure.extendedContent_apply_measurable (measurable index)]
      exact measure.apply_measurable (measurable index)
    exact ENNReal.le_trans bound
      (ENNReal.tsum_le_tsum (fun index => by
        rw [terms index]
        exact ENNReal.le_refl _))
  exact ⟨ENNReal.le_trans unionBound costBelow.1,
    fun reverse => costBelow.2 (ENNReal.le_trans reverse unionBound)⟩

/-- Every outer-null set is contained in a measurable null set without
measure-completeness hypotheses. -/
public theorem NullSet.exists_measurable_superset {measure : Measure space}
    {set : Set alpha} (nullSet : measure.NullSet set) :
    ∃ superset : Set alpha, space.Measurable superset ∧
      Set.Subset set superset ∧ measure.NullSet superset := by
  classical
  rcases ENNReal.exists_positive_summable_error ENNReal.one True.intro
    ENNReal.one_positive with ⟨errors, positive, summable⟩
  have covers : ∀ index, ∃ superset : Set alpha, space.Measurable superset ∧
      Set.Subset set superset ∧ ENNReal.lt (measure superset) (errors index) := by
    intro index
    apply measure.exists_measurable_superset_lt
    rw [nullSet]
    exact positive index
  let supersets : Nat → Set alpha := fun index => Classical.choose (covers index)
  have measurable : ∀ index, space.Measurable (supersets index) :=
    fun index => (Classical.choose_spec (covers index)).1
  have included : ∀ index, Set.Subset set (supersets index) :=
    fun index => (Classical.choose_spec (covers index)).2.1
  have small : ∀ index, ENNReal.le (measure (supersets index)) (errors index) :=
    fun index => (Classical.choose_spec (covers index)).2.2.1
  refine ⟨Set.iInter supersets, space.iInter measurable,
    (fun {_} member index => included index member), ?_⟩
  apply Classical.byContradiction
  intro nonzero
  have totalBound := ENNReal.le_trans
    (ENNReal.tsum_le_tsum (fun index => ENNReal.le_trans
      (measure.mono (left := Set.iInter supersets)
        (fun {_} member => member index)) (small index))) summable
  have infinite : ENNReal.tsum (fun _ : Nat => measure (Set.iInter supersets)) =
      ENNReal.top := ENNReal.tsum_const_of_ne_zero nonzero
  rw [infinite] at totalBound
  exact totalBound

end Problib.Measure.Measure
