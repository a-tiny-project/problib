module

public import Problib.QuasiBorel.Domain.FixedPoint
public import Problib.QuasiBorel.Domain.Weight
public import Problib.QuasiBorel.SFinite.Generator
public import Problib.QuasiBorel.Measurable.Sum

/-!
# Lifting a predomain with a fresh bottom

A partial computation either fails or returns a value. This module orders such
outcomes as a predomain `lift D`. Its points are failure or a defined point of
`D`, on the failure coproduct `SFinite.withFailure D.space`. Failure lies below
every outcome, and defined points compare as in `D`. The bottom is fresh even
when `D` already has one.

An increasing chain is either failure throughout, or defined from some first
stage on. Its supremum is failure in the first case, and in the second the
supremum in `D` of the values from that first stage. The coproduct's own
discrete order would make every chain constant, so it is not used. Random
elements are closed under these suprema because the first defined stage is a
measurable function of the seed.

A test on `D`, extended by zero on failure, is a continuous test on `lift D`.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.Domain.Predomain

public section

open Problib.Domain
open Problib.Real (ENNReal)
open Problib.Measure.Real (borel Carrier)
open Problib.QuasiBorel.SFinite (realSource withFailure weightSpace)

universe v

variable {D : Predomain.{0, v} realSource}

theorem sup_congr {α : Type v} (order : CPO α) {first second : Nat → α}
    (firstChain : order.Chain first) (secondChain : order.Chain second)
    (equal : first = second) : order.sup first firstChain = order.sup second secondChain := by
  subst equal
  rfl

/-! ### The lifted order -/

/-- Failure lies below every outcome; defined points compare in `D`. -/
@[expose] def liftLe (D : Predomain.{0, v} realSource) :
    Sum Unit D.space.Carrier → Sum Unit D.space.Carrier → Prop
  | .inl _, _ => True
  | .inr _, .inl _ => False
  | .inr left, .inr right => D.order.le left right

theorem liftLe_defined {left right : Sum Unit D.space.Carrier} (below : liftLe D left right)
    (defined : left.isRight = true) : right.isRight = true := by
  cases left with
  | inl _ => cases defined
  | inr _ =>
      cases right with
      | inl _ => exact False.elim below
      | inr _ => rfl

/-- A lifted point's value, read with a fallback for failure. -/
@[expose] def valueOr (fallback : D.space.Carrier) : Sum Unit D.space.Carrier → D.space.Carrier :=
  Sum.elim (fun _ => fallback) (fun value => value)

/-- The value of a defined lifted point. -/
@[expose] def definedValue : (point : Sum Unit D.space.Carrier) → point.isRight = true →
    D.space.Carrier
  | .inr value, _ => value
  | .inl _, impossible => by cases impossible

theorem defined_after {chain : Nat → Sum Unit D.space.Carrier}
    (increasing : ∀ first second, first ≤ second → liftLe D (chain first) (chain second))
    {stage : Nat} (defined : (chain stage).isRight = true) (extra : Nat) :
    (chain (stage + extra)).isRight = true :=
  liftLe_defined (increasing _ _ (Nat.le_add_right stage extra)) defined

/-- Values of a chain from a defined stage on. -/
@[expose] def tail (chain : Nat → Sum Unit D.space.Carrier) (stage : Nat)
    (fallback : D.space.Carrier) (extra : Nat) : D.space.Carrier :=
  valueOr fallback (chain (stage + extra))

theorem tail_eq {chain : Nat → Sum Unit D.space.Carrier} {stage extra : Nat}
    {value : D.space.Carrier} (fallback : D.space.Carrier)
    (point : chain (stage + extra) = Sum.inr value) : tail chain stage fallback extra = value := by
  unfold tail valueOr
  rw [point]
  rfl

theorem tail_chain {chain : Nat → Sum Unit D.space.Carrier}
    (increasing : ∀ first second, first ≤ second → liftLe D (chain first) (chain second))
    {stage : Nat} (defined : (chain stage).isRight = true) (fallback : D.space.Carrier) :
    D.order.Chain (tail chain stage fallback) := by
  intro first second before
  have below := increasing (stage + first) (stage + second) (Nat.add_le_add_left before stage)
  have firstDefined := defined_after increasing defined first
  have secondDefined := defined_after increasing defined second
  cases firstPoint : chain (stage + first) with
  | inl _ => rw [firstPoint] at firstDefined; cases firstDefined
  | inr firstValue =>
      cases secondPoint : chain (stage + second) with
      | inl _ => rw [secondPoint] at secondDefined; cases secondDefined
      | inr secondValue =>
          rw [tail_eq fallback firstPoint, tail_eq fallback secondPoint]
          rw [firstPoint, secondPoint] at below
          exact below

/-! ### The least stage where a property holds -/

theorem exists_leastStage {predicate : Nat → Prop} (holdsSomewhere : ∃ stage, predicate stage) :
    ∃ stage, predicate stage ∧ ∀ earlier, earlier < stage → ¬predicate earlier := by
  rcases holdsSomewhere with ⟨stage, holds⟩
  induction stage using Nat.strongRecOn with
  | ind stage induction =>
      by_cases found : ∃ earlier, earlier < stage ∧ predicate earlier
      · rcases found with ⟨earlier, before, earlierHolds⟩
        exact induction earlier before earlierHolds
      · exact ⟨stage, holds, fun earlier before earlierHolds =>
          found ⟨earlier, before, earlierHolds⟩⟩

/-- The least stage where a property holds, given that it holds somewhere. -/
@[expose] noncomputable def leastStage {predicate : Nat → Prop}
    (holdsSomewhere : ∃ stage, predicate stage) : Nat :=
  Classical.choose (exists_leastStage holdsSomewhere)

theorem leastStage_spec {predicate : Nat → Prop} (holdsSomewhere : ∃ stage, predicate stage) :
    predicate (leastStage holdsSomewhere) :=
  (Classical.choose_spec (exists_leastStage holdsSomewhere)).1

theorem leastStage_le {predicate : Nat → Prop} (holdsSomewhere : ∃ stage, predicate stage)
    {stage : Nat} (holds : predicate stage) : leastStage holdsSomewhere ≤ stage :=
  Nat.le_of_not_lt (fun before => (Classical.choose_spec (exists_leastStage holdsSomewhere)).2 stage
    before holds)

theorem leastStage_eq_iff {predicate : Nat → Prop} (holdsSomewhere : ∃ stage, predicate stage)
    {stage : Nat} :
    leastStage holdsSomewhere = stage ↔
      predicate stage ∧ ∀ earlier, earlier < stage → ¬predicate earlier := by
  constructor
  · intro equal
    rw [← equal]
    exact Classical.choose_spec (exists_leastStage holdsSomewhere)
  · intro ⟨holds, first⟩
    exact Nat.le_antisymm (leastStage_le holdsSomewhere holds)
      (Nat.le_of_not_lt (fun before => first _ before (leastStage_spec holdsSomewhere)))

/-- Supremum of a lifted chain: the supremum in `D` from the first defined
stage, or failure when no stage is defined. -/
@[expose] noncomputable def liftSup (chain : Nat → Sum Unit D.space.Carrier)
    (increasing : ∀ first second, first ≤ second → liftLe D (chain first) (chain second)) :
    Sum Unit D.space.Carrier := by
  classical
  exact if defined : ∃ stage, (chain stage).isRight = true then
    Sum.inr (D.order.sup
      (tail chain (leastStage defined) (definedValue _ (leastStage_spec defined)))
      (tail_chain increasing (leastStage_spec defined) _))
  else Sum.inl ()

theorem liftSup_of_defined {chain : Nat → Sum Unit D.space.Carrier}
    (increasing : ∀ first second, first ≤ second → liftLe D (chain first) (chain second))
    (defined : ∃ stage, (chain stage).isRight = true) :
    liftSup chain increasing = Sum.inr (D.order.sup
      (tail chain (leastStage defined) (definedValue _ (leastStage_spec defined)))
      (tail_chain increasing (leastStage_spec defined) _)) := by
  classical
  unfold liftSup
  rw [dite_eq_left defined]

theorem liftSup_of_undefined {chain : Nat → Sum Unit D.space.Carrier}
    (increasing : ∀ first second, first ≤ second → liftLe D (chain first) (chain second))
    (undefined : ¬∃ stage, (chain stage).isRight = true) :
    liftSup chain increasing = Sum.inl () := by
  classical
  unfold liftSup
  rw [dite_eq_right undefined]

theorem undefined_stage {chain : Nat → Sum Unit D.space.Carrier}
    (undefined : ¬∃ stage, (chain stage).isRight = true) (stage : Nat) :
    chain stage = Sum.inl () := by
  cases point : chain stage with
  | inl failed => cases failed; rfl
  | inr _ => exact (undefined ⟨stage, by rw [point]; rfl⟩).elim

/-- The lifted order, with a fresh bottom. -/
@[expose] noncomputable def liftOrder (D : Predomain.{0, v} realSource) :
    CPO (Sum Unit D.space.Carrier) where
  le := liftLe D
  refl := fun
    | .inl _ => True.intro
    | .inr value => D.order.refl value
  trans := by
    intro left middle right first second
    cases left with
    | inl _ => exact True.intro
    | inr _ =>
        cases middle with
        | inl _ => exact False.elim first
        | inr _ =>
            cases right with
            | inl _ => exact False.elim second
            | inr _ => exact D.order.trans first second
  antisymm := by
    intro left right first second
    cases left with
    | inl leftUnit =>
        cases right with
        | inl rightUnit => cases leftUnit; cases rightUnit; rfl
        | inr _ => exact False.elim second
    | inr _ =>
        cases right with
        | inl _ => exact False.elim first
        | inr _ => exact congrArg Sum.inr (D.order.antisymm first second)
  sup := liftSup
  below_sup := by
    intro chain increasing stage
    cases point : chain stage with
    | inl _ => exact True.intro
    | inr value =>
        have defined : ∃ stage, (chain stage).isRight = true := ⟨stage, by rw [point]; rfl⟩
        rw [liftSup_of_defined increasing defined]
        obtain ⟨extra, equal⟩ := Nat.exists_eq_add_of_le
          (leastStage_le defined (stage := stage) (by rw [point]; rfl))
        have below := D.order.below_sup _ (tail_chain increasing (leastStage_spec defined)
          (definedValue _ (leastStage_spec defined))) extra
        rw [tail_eq _ (by rw [← equal]; exact point)] at below
        exact below
  sup_least := by
    intro chain increasing upper below
    by_cases defined : ∃ stage, (chain stage).isRight = true
    · rw [liftSup_of_defined increasing defined]
      have firstDefined := leastStage_spec defined
      cases upper with
      | inl _ =>
          have impossible := liftLe_defined (below (leastStage defined)) firstDefined
          cases impossible
      | inr top =>
          apply D.order.sup_least
          intro extra
          have atStage := below (leastStage defined + extra)
          have definedHere := defined_after increasing firstDefined extra
          cases point : chain (leastStage defined + extra) with
          | inl _ => rw [point] at definedHere; cases definedHere
          | inr value =>
              rw [tail_eq _ point]
              rw [point] at atStage
              exact atStage
    · rw [liftSup_of_undefined increasing defined]
      exact True.intro

/-! ### Random suprema -/

/-- Reading the second point of a pair with a fallback, guarded by the first:
the fallback when the first point fails. -/
@[expose] def guardedMap (fallback : D.space.Carrier) :
    QuasiBorel.Hom (Space.product (withFailure D.space) (withFailure D.space)) D.space :=
  Space.uncurry (Space.copair
    (QuasiBorel.Hom.constant _ (Space.exponential (withFailure D.space) D.space)
      (QuasiBorel.Hom.constant _ _ fallback))
    (QuasiBorel.Hom.constant _ (Space.exponential (withFailure D.space) D.space)
      (Space.copair (QuasiBorel.Hom.constant _ _ fallback)
        (QuasiBorel.Hom.identity D.space))))

/-- `guardedMap` read at a pair. -/
@[expose] def guarded (fallback : D.space.Carrier)
    (pair : Sum Unit D.space.Carrier × Sum Unit D.space.Carrier) : D.space.Carrier :=
  guardedMap fallback pair

theorem guarded_failure (fallback : D.space.Carrier) (failed : Unit)
    (point : Sum Unit D.space.Carrier) : guarded fallback (Sum.inl failed, point) = fallback := rfl

theorem guarded_up (fallback value : D.space.Carrier) (point : Sum Unit D.space.Carrier) :
    guarded fallback (Sum.inr value, point) = valueOr fallback point := by
  cases point <;> rfl

theorem guarded_chain (fallback : D.space.Carrier) {chain : Nat → Sum Unit D.space.Carrier}
    (increasing : ∀ first second, first ≤ second → liftLe D (chain first) (chain second))
    (stage : Nat) :
    D.order.Chain (fun extra => guarded fallback (chain stage, chain (stage + extra))) := by
  cases point : chain stage with
  | inl failed =>
      intro first second _
      simp only [guarded_failure]
      exact D.order.refl fallback
  | inr value =>
      have defined : (chain stage).isRight = true := by rw [point]; rfl
      have equal : (fun extra => guarded fallback (Sum.inr value, chain (stage + extra))) =
          tail chain stage fallback :=
        funext (fun extra => guarded_up fallback value _)
      rw [equal]
      exact tail_chain increasing defined fallback

/-- One plus the first defined stage of a chain at a seed, or zero. -/
@[expose] noncomputable def firstStage (chain : Nat → Carrier → Sum Unit D.space.Carrier)
    (seed : Carrier) : Nat := by
  classical
  exact if defined : ∃ stage, (chain stage seed).isRight = true then leastStage defined + 1 else 0

theorem firstStage_eq_zero_iff (chain : Nat → Carrier → Sum Unit D.space.Carrier)
    (seed : Carrier) :
    firstStage chain seed = 0 ↔ ∀ stage, ¬(chain stage seed).isRight = true := by
  classical
  unfold firstStage
  by_cases defined : ∃ stage, (chain stage seed).isRight = true
  · rw [dite_eq_left defined]
    exact ⟨fun equal => (Nat.succ_ne_zero _ equal).elim,
      fun undefined => (undefined _ (leastStage_spec defined)).elim⟩
  · rw [dite_eq_right defined]
    exact ⟨fun _ stage isDefined => defined ⟨stage, isDefined⟩, fun _ => rfl⟩

theorem firstStage_eq_succ_iff (chain : Nat → Carrier → Sum Unit D.space.Carrier)
    (seed : Carrier) (stage : Nat) :
    firstStage chain seed = stage + 1 ↔ (chain stage seed).isRight = true ∧
      ∀ earlier, earlier < stage → ¬(chain earlier seed).isRight = true := by
  classical
  unfold firstStage
  by_cases defined : ∃ stage, (chain stage seed).isRight = true
  · rw [dite_eq_left defined, Nat.add_right_cancel_iff, leastStage_eq_iff]
  · rw [dite_eq_right defined]
    exact ⟨fun equal => (Nat.succ_ne_zero _ equal.symm).elim,
      fun found => (defined ⟨stage, found.1⟩).elim⟩

theorem defined_measurable {random : Carrier → Sum Unit D.space.Carrier}
    (accepted : (withFailure D.space).Random random) :
    borel.Measurable (fun seed => (random seed).isRight = true) := by
  have regionMeasurable : (Problib.Measure.Space.sum (Space.terminal realSource).toMeasurable
      D.space.toMeasurable).Measurable
      (fun point : Sum Unit D.space.Carrier => point.isRight = true) := by
    constructor
    · have empty : Problib.Measure.Set.preimage Sum.inl
          (fun point : Sum Unit D.space.Carrier => point.isRight = true) =
          Problib.Measure.Set.empty := by
        apply Problib.Measure.Set.ext
        intro failed
        exact ⟨fun impossible => (by cases impossible), False.elim⟩
      rw [empty]
      exact Problib.Measure.Space.empty _
    · have whole : Problib.Measure.Set.preimage Sum.inr
          (fun point : Sum Unit D.space.Carrier => point.isRight = true) =
          Problib.Measure.Set.univ := by
        apply Problib.Measure.Set.ext
        intro value
        exact ⟨fun _ => True.intro, fun _ => rfl⟩
      rw [whole]
      exact Problib.Measure.Space.univ _
  exact SumRandom.measurable accepted regionMeasurable

theorem firstStage_partition (chain : Nat → Carrier → Sum Unit D.space.Carrier)
    (accepted : ∀ stage, (withFailure D.space).Random (chain stage)) :
    realSource.Partition (firstStage chain) := by
  classical
  show ∀ index, borel.Measurable (fun seed => firstStage chain seed = index)
  have undefinedBefore : ∀ stage, borel.Measurable (fun seed =>
      ∀ earlier, earlier < stage → ¬(chain earlier seed).isRight = true) := by
    intro stage
    have equal : (fun seed => ∀ earlier, earlier < stage →
        ¬(chain earlier seed).isRight = true) =
        Problib.Measure.Set.iInter (fun earlier => fun seed =>
          earlier < stage → ¬(chain earlier seed).isRight = true) := rfl
    rw [equal]
    apply Problib.Measure.Space.iInter
    intro earlier
    by_cases before : earlier < stage
    · have complement : (fun seed => earlier < stage → ¬(chain earlier seed).isRight = true) =
          Problib.Measure.Set.complement (fun seed => (chain earlier seed).isRight = true) :=
        Problib.Measure.Set.ext (fun seed => ⟨fun outside => outside before,
          fun outside _ => outside⟩)
      rw [complement]
      exact borel.complement (defined_measurable (accepted earlier))
    · have whole : (fun seed => earlier < stage → ¬(chain earlier seed).isRight = true) =
          Problib.Measure.Set.univ :=
        Problib.Measure.Set.ext (fun seed => ⟨fun _ => True.intro,
          fun _ inside => (before inside).elim⟩)
      rw [whole]
      exact borel.univ
  intro index
  cases index with
  | zero =>
      have equal : (fun seed => firstStage chain seed = 0) =
          Problib.Measure.Set.iInter (fun stage => Problib.Measure.Set.complement
            (fun seed => (chain stage seed).isRight = true)) :=
        Problib.Measure.Set.ext (fun seed => firstStage_eq_zero_iff chain seed)
      rw [equal]
      exact borel.iInter (fun stage => borel.complement (defined_measurable (accepted stage)))
  | succ stage =>
      have equal : (fun seed => firstStage chain seed = stage + 1) =
          Problib.Measure.Set.inter (fun seed => (chain stage seed).isRight = true)
            (fun seed => ∀ earlier, earlier < stage → ¬(chain earlier seed).isRight = true) :=
        Problib.Measure.Set.ext (fun seed => firstStage_eq_succ_iff chain seed stage)
      rw [equal]
      exact borel.inter (defined_measurable (accepted stage)) (undefinedBefore stage)

theorem lift_random_sup (chain : Nat → Carrier → Sum Unit D.space.Carrier)
    (increasing : ∀ seed, (liftOrder D).Chain (fun stage => chain stage seed))
    (accepted : ∀ stage, (withFailure D.space).Random (chain stage)) :
    (withFailure D.space).Random
      (fun seed => (liftOrder D).sup (fun stage => chain stage seed) (increasing seed)) := by
  classical
  by_cases inhabited : Nonempty D.space.Carrier
  · obtain ⟨fallback⟩ := inhabited
    let branch : Nat → Carrier → Sum Unit D.space.Carrier := fun
      | 0 => fun _ => Sum.inl ()
      | stage + 1 => fun seed => Sum.inr (D.order.sup
          (fun extra => guarded fallback (chain stage seed, chain (stage + extra) seed))
          (guarded_chain fallback (increasing seed) stage))
    have branchRandom : ∀ index, (withFailure D.space).Random (branch index) := by
      intro index
      cases index with
      | zero => exact (withFailure D.space).constant (Sum.inl ())
      | succ stage =>
          refine SumRandom.inr (D.random_sup
            (fun extra seed => guarded fallback (chain stage seed, chain (stage + extra) seed))
            (fun seed => guarded_chain fallback (increasing seed) stage) ?_)
          intro extra
          exact (guardedMap fallback).map_random
            (show (Space.product (withFailure D.space) (withFailure D.space)).Random
              (fun seed => (chain stage seed, chain (stage + extra) seed)) from
              ⟨accepted stage, accepted (stage + extra)⟩)
    have equal : (fun seed => (liftOrder D).sup (fun stage => chain stage seed) (increasing seed)) =
        fun seed => branch (firstStage chain seed) seed := by
      funext seed
      change liftSup (fun stage => chain stage seed) (increasing seed) = _
      cases count : firstStage chain seed with
      | zero =>
          have undefined := (firstStage_eq_zero_iff chain seed).mp count
          rw [liftSup_of_undefined (chain := fun stage => chain stage seed) (increasing seed)
            (fun ⟨stage, isDefined⟩ => undefined stage isDefined)]
      | succ stage =>
          have found := (firstStage_eq_succ_iff chain seed stage).mp count
          have defined : ∃ stage, (chain stage seed).isRight = true := ⟨stage, found.1⟩
          have first : leastStage defined = stage := (leastStage_eq_iff defined).mpr found
          rw [liftSup_of_defined (chain := fun stage => chain stage seed) (increasing seed) defined]
          change Sum.inr _ = Sum.inr _
          apply congrArg Sum.inr
          apply sup_congr
          funext extra
          have definedHere := defined_after (increasing seed) found.1 extra
          cases point : chain (stage + extra) seed with
          | inl _ => rw [point] at definedHere; cases definedHere
          | inr value =>
              rw [tail_eq (chain := fun stage => chain stage seed) (stage := leastStage defined)
                (extra := extra) (value := value) _ (by rw [first]; exact point)]
              cases stagePoint : chain stage seed with
              | inl _ => rw [stagePoint] at found; cases found.1
              | inr _ => rw [guarded_up]; rfl
    rw [equal]
    exact (withFailure D.space).piecewise (firstStage_partition chain accepted) branchRandom
  · have equal :
        (fun seed => (liftOrder D).sup (fun stage => chain stage seed) (increasing seed)) =
          fun _ => Sum.inl () := by
      funext seed
      change liftSup (fun stage => chain stage seed) (increasing seed) = _
      apply liftSup_of_undefined
      rintro ⟨stage, isDefined⟩
      cases point : chain stage seed with
      | inl _ => rw [point] at isDefined; cases isDefined
      | inr value => exact inhabited ⟨value⟩
    rw [equal]
    exact (withFailure D.space).constant (Sum.inl ())

/-- The lift of `D`: failure or a defined point, with a fresh bottom. -/
@[expose] noncomputable def lift (D : Predomain.{0, v} realSource) : Predomain realSource where
  space := withFailure D.space
  order := liftOrder D
  random_sup := lift_random_sup

/-- Failure is the bottom of the lift. -/
@[expose] noncomputable def liftPointed (D : Predomain.{0, v} realSource) :
    Pointed (lift D).order where
  bottom := Sum.inl ()
  below := fun _ => True.intro

theorem lift_le_up (left right : D.space.Carrier) :
    (lift D).order.le (Sum.inr left) (Sum.inr right) ↔ D.order.le left right := Iff.rfl

theorem lift_sup_undefined (chain : Nat → Sum Unit D.space.Carrier)
    (increasing : (lift D).order.Chain chain) (undefined : ∀ stage, chain stage = Sum.inl ()) :
    (lift D).order.sup chain increasing = Sum.inl () :=
  liftSup_of_undefined increasing (fun ⟨stage, isDefined⟩ => by
    rw [undefined stage] at isDefined
    cases isDefined)

/-- A defined point, as a continuous map into the lift. -/
@[expose] noncomputable def up (D : Predomain.{0, v} realSource) : Hom D (lift D) :=
  ⟨Space.inr _ _, {
    monotone := fun below => below
    preserves := by
      intro chain increasing
      have defined : ∃ stage, ((fun stage => (Sum.inr (chain stage) :
          Sum Unit D.space.Carrier)) stage).isRight = true := ⟨0, rfl⟩
      change Sum.inr _ = liftSup (fun stage => Sum.inr (chain stage))
        (fun first second order => increasing first second order)
      rw [liftSup_of_defined (chain := fun stage => Sum.inr (chain stage))
        (fun first second order => increasing first second order) defined]
      have first : leastStage defined = 0 := Nat.le_zero.mp (leastStage_le defined rfl)
      apply congrArg Sum.inr
      apply sup_congr
      funext extra
      rw [tail_eq (chain := fun stage => Sum.inr (chain stage)) (stage := leastStage defined)
        (extra := extra) (value := chain extra) _ (by rw [first, Nat.zero_add])] }⟩

theorem up_ne_bottom (point : D.space.Carrier) :
    up D point ≠ (liftPointed D).bottom := fun equal => by cases equal

/-! ### Zero extension of tests -/

/-- A test on `D` read on lifted points, zero on failure, jointly in the test
and the point. -/
@[expose] noncomputable def extendMap (D : Predomain.{0, v} realSource) :
    QuasiBorel.Hom (Space.product (exponential D weight).space (lift D).space) weightSpace :=
  QuasiBorel.Hom.comp (Space.evaluate (exponential D weight).space weightSpace)
    (Space.pair
      (QuasiBorel.Hom.comp
        (Space.copair
          (QuasiBorel.Hom.constant _ (Space.exponential (exponential D weight).space weightSpace)
            (QuasiBorel.Hom.constant _ weightSpace ENNReal.zero))
          (Space.curry (QuasiBorel.Hom.comp (evaluate D weight).val
            (Space.swap D.space (exponential D weight).space))))
        (Space.second (exponential D weight).space (lift D).space))
      (Space.first (exponential D weight).space (lift D).space))

theorem extendMap_failure (test : Hom D weight) (failed : Unit) :
    extendMap D (test, Sum.inl failed) = ENNReal.zero := rfl

theorem extendMap_up (test : Hom D weight) (point : D.space.Carrier) :
    extendMap D (test, Sum.inr point) = test point := rfl

theorem extend_le_iSup {test : Hom D weight} {chain : Nat → Sum Unit D.space.Carrier}
    (increasing : (lift D).order.Chain chain)
    (defined : ∃ stage, (chain stage).isRight = true) :
    ENNReal.le (extendMap D (test, (lift D).order.sup chain increasing))
      (ENNReal.iSup (fun stage => extendMap D (test, chain stage))) := by
  change ENNReal.le (extendMap D (test, liftSup chain increasing)) _
  rw [liftSup_of_defined increasing defined, extendMap_up,
    test.property.preserves _ (tail_chain increasing (leastStage_spec defined) _)]
  apply ENNReal.iSup_le
  intro extra
  have definedHere := defined_after increasing (leastStage_spec defined) extra
  cases point : chain (leastStage defined + extra) with
  | inl _ => rw [point] at definedHere; cases definedHere
  | inr value =>
      rw [tail_eq _ point]
      have below := ENNReal.le_iSup (fun stage => extendMap D (test, chain stage))
        (leastStage defined + extra)
      rw [point] at below
      exact below

/-- The zero extension of a continuous test is continuous on the lift. -/
theorem extend_continuous (test : Hom D weight) :
    (lift D).order.Continuous weight.order (fun point => extendMap D (test, point)) where
  monotone := by
    intro left right below
    cases left with
    | inl _ => exact ENNReal.zero_le _
    | inr _ =>
        cases right with
        | inl _ => exact False.elim below
        | inr _ => exact test.property.monotone below
  preserves := by
    intro chain increasing
    change extendMap D (test, (lift D).order.sup chain increasing) =
      ENNReal.iSup (fun stage => extendMap D (test, chain stage))
    by_cases defined : ∃ stage, (chain stage).isRight = true
    · apply ENNReal.le_antisymm (extend_le_iSup increasing defined)
      apply ENNReal.iSup_le
      intro stage
      have below := (lift D).order.below_sup chain increasing stage
      cases point : chain stage with
      | inl _ => exact ENNReal.zero_le _
      | inr value =>
          rw [point] at below
          change liftLe D (Sum.inr value) (liftSup chain increasing) at below
          change ENNReal.le _ (extendMap D (test, liftSup chain increasing))
          rw [liftSup_of_defined increasing defined] at below ⊢
          exact test.property.monotone below
    · have undefined := undefined_stage defined
      rw [lift_sup_undefined chain increasing undefined]
      have zeros : (fun stage => extendMap D (test, chain stage)) = fun _ => ENNReal.zero :=
        funext (fun stage => by rw [undefined stage]; rfl)
      rw [zeros]
      exact (ENNReal.iSup_const _).symm

/-- The zero extension of a test, a continuous test on the lift. -/
@[expose] noncomputable def extend (test : Hom D weight) : Hom (lift D) weight :=
  ⟨QuasiBorel.Hom.comp (extendMap D)
      (Space.pair (QuasiBorel.Hom.constant _ _ test) (QuasiBorel.Hom.identity _)),
    extend_continuous test⟩

theorem extend_failure (test : Hom D weight) : extend test (Sum.inl ()) = ENNReal.zero := rfl

theorem extend_up (test : Hom D weight) (point : D.space.Carrier) :
    extend test (Sum.inr point) = test point := rfl

theorem extend_apply (test : Hom D weight) (point : (lift D).space.Carrier) :
    extend test point = extendMap D (test, point) := rfl

end

end Problib.QuasiBorel.Domain.Predomain
