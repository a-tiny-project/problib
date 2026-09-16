module

public import Foundations.Measure.Decomposition.ZeroInfinity.Basic
public import Foundations.Measure.Additive.Partition
public import Foundations.Measure.Additive.SFinite

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Every zero-infinity set under a sigma-finite measure is a null set. -/
public theorem IsZeroInfinitySet.null_of_sigmaFinite {measure : Measure space}
    {region : Set alpha} (zeroInfinity : Measure.IsZeroInfinitySet measure region)
    (finite : Measure.SigmaFinite measure) : measure.NullSet region := by
  have nullPieces : ∀ index, measure.NullSet (Set.inter region (finite.sets index)) := by
    intro index
    have measurable := space.inter zeroInfinity.measurable (finite.measurable index)
    rcases zeroInfinity.subsets_zero_or_top measurable (fun {_} member => member.1) with
      zero | infinite
    · exact zero
    · have pieceFinite := ENNReal.finiteOfLe
        (measure.mono (show Set.Subset (Set.inter region (finite.sets index))
          (finite.sets index) from fun {_} member => member.2)) (finite.finite index)
      exact False.elim ((ENNReal.finiteIffNeTop.mp pieceFinite) infinite)
  apply (Measure.NullSet.iUnion nullPieces).mono
  intro value member
  have covered : Set.iUnion finite.sets value := by rw [finite.cover]; exact True.intro
  rcases covered with ⟨index, contained⟩
  exact ⟨index, member, contained⟩

/-- Restricting a measure to a measurable region preserves zero-infinity sets. -/
public theorem IsZeroInfinitySet.restrict {measure : Measure space} {region : Set alpha}
    (zeroInfinity : Measure.IsZeroInfinitySet measure region)
    {restriction : Set alpha} (measurable : space.Measurable restriction) :
    Measure.IsZeroInfinitySet (measure.restrict restriction) region := by
  refine ⟨zeroInfinity.measurable, ?_⟩
  intro subset subsetMeasurable included
  rw [measure.restrict_apply restriction subsetMeasurable]
  exact zeroInfinity.subsets_zero_or_top (space.inter subsetMeasurable measurable)
    (fun {_} member => included member.1)

/-- Any two greatest zero-infinity sets induce identical restricted measures on
their complements. -/
public theorem TopZeroInfinitySet.restrict_complement_eq {measure : Measure space}
    (left right : TopZeroInfinitySet measure) :
    measure.restrict (Set.complement left.set) =
      measure.restrict (Set.complement right.set) := by
  classical
  apply Measure.ext
  intro set measurable
  rw [measure.restrict_apply _ measurable, measure.restrict_apply _ measurable]
  apply measure_eq_of_null_difference
  · apply (show measure.NullSet (Set.difference right.set left.set) from
      left.greatest right.zeroInfinity).mono
    intro value member
    exact ⟨Classical.byContradiction (fun absent => member.2 ⟨member.1.1, absent⟩),
      member.1.2⟩
  · apply (show measure.NullSet (Set.difference left.set right.set) from
      right.greatest left.zeroInfinity).mono
    intro value member
    exact ⟨Classical.byContradiction (fun absent => member.2 ⟨member.1.1, absent⟩),
      member.1.2⟩

/-- A measurable null set is a zero-infinity set. -/
public theorem IsZeroInfinitySet.of_null {measure : Measure space} {region : Set alpha}
    (measurable : space.Measurable region) (null : measure.NullSet region) :
    IsZeroInfinitySet measure region :=
  ⟨measurable, fun _ included => Or.inl (null.mono included)⟩

/-- A measurable set whose difference from a zero-infinity set is null is also a
zero-infinity set. -/
public theorem IsZeroInfinitySet.of_null_difference {measure : Measure space} {region cover : Set alpha}
    (measurable : space.Measurable region) (covered : Measure.IsZeroInfinitySet measure cover)
    (nullDifference : measure.NullSet (Set.difference region cover)) :
    Measure.IsZeroInfinitySet measure region := by
  refine ⟨measurable, ?_⟩
  intro subset subsetMeasurable included
  have nullSubset : measure.NullSet (Set.difference subset cover) :=
    nullDifference.mono (fun {_} member => ⟨included member.1, member.2⟩)
  have same := measure.inter_add_difference subset covered.measurable
  rw [nullSubset, ENNReal.addZero] at same
  rw [← same]
  exact covered.subsets_zero_or_top (space.inter subsetMeasurable covered.measurable)
    (fun {_} member => member.2)

/-- Any two greatest zero-infinity set certificates induce identical restricted
measures on their zero-infinity regions without finiteness premises. -/
public theorem TopZeroInfinitySet.restrict_eq {measure : Measure space}
    (left right : Measure.TopZeroInfinitySet measure) :
    measure.restrict left.set = measure.restrict right.set := by
  apply Measure.ext
  intro set setMeasurable
  rw [measure.restrict_apply _ setMeasurable, measure.restrict_apply _ setMeasurable]
  apply Measure.measure_eq_of_null_difference
  · apply Measure.NullSet.mono (right.greatest left.zeroInfinity)
    intro value member
    exact ⟨member.1.2, fun inside => member.2 ⟨member.1.1, inside⟩⟩
  · apply Measure.NullSet.mono (left.greatest right.zeroInfinity)
    intro value member
    exact ⟨member.1.2, fun inside => member.2 ⟨member.1.1, inside⟩⟩

/-- A restricted measure is zero-infinity on the whole space if and only if the original measure is zero-infinity on the restriction region. -/
public theorem isZeroInfinitySet_restrict_univ_iff (measure : Measure space) {region : Set alpha}
    (measurable : space.Measurable region) :
    IsZeroInfinitySet (measure.restrict region) Set.univ ↔ IsZeroInfinitySet measure region := by
  constructor
  · intro pure
    refine ⟨measurable, ?_⟩
    intro set setMeasurable included
    have equal : Set.inter set region = set := by
      apply Set.ext
      intro input
      exact ⟨fun member => member.1, fun member => ⟨member, included member⟩⟩
    have cases := pure.subsets_zero_or_top setMeasurable (Set.subset_univ _)
    rw [Measure.restrict_apply _ _ setMeasurable, equal] at cases
    exact cases
  · intro pure
    refine ⟨space.univ, ?_⟩
    intro set setMeasurable _
    rw [Measure.restrict_apply _ _ setMeasurable]
    exact pure.subsets_zero_or_top (space.inter setMeasurable measurable) (fun _ member => member.2)

/-- Scaling an arbitrary measure by infinity yields a zero-infinity measure on the whole space. -/
public theorem IsZeroInfinitySet.smul_top (measure : Measure space) :
    IsZeroInfinitySet (Measure.smul ENNReal.top measure) Set.univ := by
  refine ⟨space.univ, ?_⟩
  intro set measurable _
  rw [Measure.smul_apply_measurable _ _ measurable]
  classical
  by_cases zero : measure set = ENNReal.zero
  · exact Or.inl (by rw [zero, ENNReal.mulZero])
  · exact Or.inr (ENNReal.topMulOfNeZero zero)

end Foundations.Measure.Measure
