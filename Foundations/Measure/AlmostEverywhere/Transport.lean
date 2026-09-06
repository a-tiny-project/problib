module

public import Foundations.Measure.AlmostEverywhere.Basic
public import Foundations.Measure.Additive.Map
public import Foundations.Measure.Additive.Restrict

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u v w

variable {alpha : Type u} {beta : Type v} {gamma : Sort w}
  {source : Space alpha} {target : Space beta} {measure : Measure source}

public theorem NullSet.preimage_of_map (function : alpha → beta)
    (measurable : MeasurableMap source target function) {set : Set beta}
    (nullSet : (measure.map function measurable).NullSet set) :
    measure.NullSet (Set.preimage function set) := by
  rcases nullSet.exists_measurable_superset with
    ⟨superset, supersetMeasurable, included, supersetNull⟩
  have preimageNull : measure.NullSet (Set.preimage function superset) := by
    rw [NullSet, ← measure.map_apply function measurable supersetMeasurable]
    exact supersetNull
  exact preimageNull.mono (fun {_} member => included member)

public theorem AE.of_map (function : alpha → beta)
    (measurable : MeasurableMap source target function) {predicate : beta → Prop}
    (holds : (measure.map function measurable).AE predicate) :
    measure.AE (fun value => predicate (function value)) :=
  NullSet.preimage_of_map function measurable holds

/-- Pulling an almost-everywhere predicate back along a measurable map is
equivalent to pushforward satisfaction when the target predicate is
measurable. -/
public theorem ae_map_iff (function : alpha → beta)
    (measurable : MeasurableMap source target function) {predicate : beta → Prop}
    (predicateMeasurable : target.Measurable predicate) :
    (measure.map function measurable).AE predicate ↔
      measure.AE (fun value => predicate (function value)) := by
  unfold AE NullSet
  rw [measure.map_apply function measurable
    (target.complement predicateMeasurable)]
  rfl

public theorem AE.restrict {predicate : alpha → Prop}
    (holds : measure.AE predicate) (region : Set alpha) :
    (measure.restrict region).AE predicate :=
  NullSet.restrict holds region

/-- A measurable region holds almost everywhere under restriction of the measure
to that region. -/
public theorem ae_restrict_mem (measure : Measure source) {region : Set alpha}
    (measurable : source.Measurable region) :
    (measure.restrict region).AE region := by
  change (measure.restrict region) (Set.complement region) = ENNReal.zero
  rw [measure.restrict_apply region (source.complement measurable)]
  have empty : Set.inter (Set.complement region) region = Set.empty := by
    apply Set.ext
    intro value
    exact ⟨fun member => member.1 member.2, False.elim⟩
  rw [empty, measure.empty_apply]

public theorem AEEq.restrict {left right : alpha → gamma}
    (equal : measure.AEEq left right) (region : Set alpha) :
    (measure.restrict region).AEEq left right :=
  AE.restrict equal region

public theorem AEEq.of_map (function : alpha → beta)
    (measurable : MeasurableMap source target function) {left right : beta → gamma}
    (equal : (measure.map function measurable).AEEq left right) :
    measure.AEEq (fun value => left (function value))
      (fun value => right (function value)) :=
  AE.of_map function measurable equal

/-- Restricting a measure to two almost-everywhere equal arbitrary sets yields
identical restricted measures without measurability or finiteness premises. -/
public theorem restrict_congr_ae {left right : Set alpha}
    (equal : measure.AEEq left right) :
    measure.restrict left = measure.restrict right := by
  apply Measure.ext
  intro set setMeasurable
  rw [measure.restrict_apply _ setMeasurable, measure.restrict_apply _ setMeasurable]
  apply Measure.measure_eq_of_null_difference
  · apply Measure.NullSet.mono equal
    intro value member agreement
    exact member.2 ⟨member.1.1, Eq.mp agreement member.1.2⟩
  · apply Measure.NullSet.mono equal
    intro value member agreement
    exact member.2 ⟨member.1.1, Eq.mpr agreement member.1.2⟩

/-- A set that is null under two measures is null under their sum. -/
public theorem NullSet.add {left right : Measure source} {set : Set alpha}
    (leftNull : left.NullSet set) (rightNull : right.NullSet set) :
    (Measure.add left right).NullSet set := by
  rcases leftNull.exists_measurable_superset with ⟨leftSet, leftMeasurable, leftIncludes, leftZero⟩
  rcases rightNull.exists_measurable_superset with ⟨rightSet, rightMeasurable, rightIncludes, rightZero⟩
  have leftInter : left.NullSet (Set.inter leftSet rightSet) :=
    Measure.NullSet.mono leftZero (fun _ member => member.1)
  have rightInter : right.NullSet (Set.inter leftSet rightSet) :=
    Measure.NullSet.mono rightZero (fun _ member => member.2)
  have combined : (Measure.add left right).NullSet (Set.inter leftSet rightSet) := by
    rw [Measure.NullSet, Measure.add_apply_measurable _ _ (source.inter leftMeasurable rightMeasurable),
      leftInter, rightInter, ENNReal.addZero]
  exact combined.mono (fun _ member => ⟨leftIncludes member, rightIncludes member⟩)

/-- An almost-everywhere predicate under two measures holds almost everywhere under their sum. -/
public theorem AE.add {left right : Measure source} {predicate : alpha → Prop}
    (leftHolds : left.AE predicate) (rightHolds : right.AE predicate) :
    (Measure.add left right).AE predicate :=
  NullSet.add leftHolds rightHolds

end Foundations.Measure.Measure
