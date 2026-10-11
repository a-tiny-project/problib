module

public import Problib.Measure.Exchangeable.Urn
public import Problib.Measure.Configuration.Position
public import Problib.Measure.Kernel.Iteration.Basic
public import Problib.Measure.Integral.Density.Zero
public import Problib.Measure.Kernel.Precomp

set_option autoImplicit false

/-!
# Sampled urns

A sampled urn carries a kernel that draws the next observation from the
statistic. At a valid statistic the draw is a probability law with density
`predictive s` against a declared base measure. Validity holds at the initial
statistic and survives every observation the predictive allows, so it holds
almost surely after each draw (`valid_ae`). Off the valid statistics the kernel
is only required to be s-finite.

`law q n` is the law of the first `n` observations from `q`: each step draws
from the statistic of the history so far and appends the draw. `statStep` moves
a statistic by one draw, and `statLaw n` is its `n`-th power. `traceStep` and
`traceLaw n` carry the list of draws beside the statistic.
-/

namespace Problib.Measure.Exchangeable

open Problib.Real

public section

universe u v

variable {α : Type u} {Y : Space α}

/-- A sampling kernel for an urn, with density `predictive s` against `base`
at every valid statistic `s`. -/
structure Urn.Sampled (U : Urn.{u, v} Y) where
  Valid : U.Stat → Prop
  valid_measurable : U.statSpace.Measurable Valid
  valid_init : Valid U.init
  valid_inc : ∀ {s y}, Valid s → U.predictive s y ≠ ENNReal.zero → Valid (U.incorporate s y)
  base : Measure Y
  baseFinite : Measure.SFinite base
  kernel : Kernel U.statSpace Y
  kernelFinite : Kernel.IsSFinite kernel
  markov : ∀ {s}, Valid s → Measure.IsProbability (kernel s)
  kernel_eq : ∀ {s}, Valid s → kernel s = base.withDensity (U.predictive s)

namespace Urn

variable {U : Urn.{u, v} Y}

/-- After a draw from a valid statistic, the statistic is almost surely valid. -/
theorem Sampled.valid_ae (S : U.Sampled) {s : U.Stat} (valid : S.Valid s) :
    (S.kernel s).AE fun y => S.Valid (U.incorporate s y) := by
  have zeroMeasurable : Y.Measurable fun y => U.predictive s y = ENNReal.zero :=
    ENNRealMeasurable.eq_set (U.predictive_at_measurable s)
      (ENNRealMeasurable.constant Y ENNReal.zero)
  apply Measure.NullSet.mono (right := fun y => U.predictive s y = ENNReal.zero)
  · change S.kernel s _ = ENNReal.zero
    rw [S.kernel_eq valid, Measure.withDensity_apply_eq_zero_iff
      (U.predictive_at_measurable s) zeroMeasurable]
    have empty : Set.inter (fun y => U.predictive s y = ENNReal.zero)
        (fun y => U.predictive s y ≠ ENNReal.zero) = Set.empty := by
      apply Set.ext
      intro y
      exact ⟨fun member => member.2 member.1, fun member => False.elim member⟩
    rw [empty]
    exact S.base.empty_apply
  · intro y invalid
    by_cases zero : U.predictive s y = ENNReal.zero
    · exact zero
    · exact False.elim (invalid (S.valid_inc valid zero))

/-- The draw kernel read at the statistic of a history from `q`. -/
@[expose] noncomputable def historyKernel (U : Urn.{u, v} Y) (S : U.Sampled) (q : U.Stat)
    (n : Nat) :
    Kernel (historySpace Y n) Y :=
  S.kernel.precomp (fun ys => U.stat q (toList ys)) (U.stat_measurable q n)

/-- The law of the first `n` observations from `q`. -/
@[expose] noncomputable def law (U : Urn.{u, v} Y) (S : U.Sampled) (q : U.Stat) :
    (n : Nat) → Measure (historySpace Y n)
  | 0 => Measure.dirac _ empty
  | n + 1 =>
      (Measure.semiproduct (law U S q n) (historyKernel U S q n)
          (S.kernelFinite.precomp _ (U.stat_measurable q n))).map
        (fun pair => snoc pair.1 pair.2) (snoc_measurable Y n)

theorem law_zero (S : U.Sampled) (q : U.Stat) : U.law S q 0 = Measure.dirac _ empty := rfl

theorem law_succ (S : U.Sampled) (q : U.Stat) (n : Nat) :
    U.law S q (n + 1) =
      (Measure.semiproduct (U.law S q n) (U.historyKernel S q n)
          (S.kernelFinite.precomp _ (U.stat_measurable q n))).map
        (fun pair => snoc pair.1 pair.2) (snoc_measurable Y n) := rfl

/-- One draw and its incorporation. -/
@[expose] noncomputable def statStep (U : Urn.{u, v} Y) (S : U.Sampled) :
    Kernel U.statSpace U.statSpace :=
  (Kernel.attach S.kernel S.kernelFinite).map (fun pair => U.incorporate pair.1 pair.2)
    U.incorporate_measurable

/-- The statistic after `n` draws. -/
@[expose] noncomputable def statLaw (U : Urn.{u, v} Y) (S : U.Sampled) (n : Nat) :
    Kernel U.statSpace U.statSpace :=
  Kernel.iterate (statStep U S) n

/-- Appending one element at the end of a list is measurable. -/
theorem append_last_measurable (Y : Space α) :
    MeasurableMap (Space.product (Space.list Y) Y) (Space.list Y)
      (fun pair => pair.1 ++ [pair.2]) := by
  have equal : (fun pair : List α × α => pair.1 ++ [pair.2]) =
      fun pair => List.reverse (pair.2 :: List.reverse pair.1) := by
    funext pair
    rw [List.reverse_cons, List.reverse_reverse]
  rw [equal]
  have reversed : MeasurableMap (Space.product (Space.list Y) Y) (Space.list Y)
      (fun pair => List.reverse pair.1) :=
    MeasurableMap.comp (before := (Prod.fst : List α × α → List α)) (reverse_measurable Y)
      (Space.first_measurable (Space.list Y) Y)
  have paired : MeasurableMap (Space.product (Space.list Y) Y)
      (Space.product Y (Space.list Y)) (fun pair => (pair.2, List.reverse pair.1)) :=
    Space.pair_measurable (Space.second_measurable (Space.list Y) Y) reversed
  have consed : MeasurableMap (Space.product (Space.list Y) Y) (Space.list Y)
      (fun pair => pair.2 :: List.reverse pair.1) :=
    fun {set} => MeasurableMap.comp
      (before := fun (pair : List α × α) => (pair.2, List.reverse pair.1))
      (ListSpace.cons_measurable Y) paired (set := set)
  exact fun {set} => MeasurableMap.comp
    (before := fun (pair : List α × α) => pair.2 :: List.reverse pair.1)
    (reverse_measurable Y) consed (set := set)

/-- The space of a list of draws beside a statistic. -/
abbrev traceSpace (U : Urn.{u, v} Y) : Space (List α × U.Stat) :=
  Space.product (Space.list Y) U.statSpace

theorem trace_next_measurable (U : Urn.{u, v} Y) :
    MeasurableMap (Space.product (traceSpace U) Y) (traceSpace U)
      (fun pair => (pair.1.1 ++ [pair.2], U.incorporate pair.1.2 pair.2)) := by
  have draws : MeasurableMap (Space.product (traceSpace U) Y) (Space.list Y)
      (fun pair => pair.1.1) :=
    MeasurableMap.comp (before := (Prod.fst : (List α × U.Stat) × α → List α × U.Stat))
      (Space.first_measurable (Space.list Y) U.statSpace)
      (Space.first_measurable (traceSpace U) Y)
  have statistic : MeasurableMap (Space.product (traceSpace U) Y) U.statSpace
      (fun pair => pair.1.2) :=
    MeasurableMap.comp (before := (Prod.fst : (List α × U.Stat) × α → List α × U.Stat))
      (Space.second_measurable (Space.list Y) U.statSpace)
      (Space.first_measurable (traceSpace U) Y)
  have drawn : MeasurableMap (Space.product (traceSpace U) Y) Y (fun pair => pair.2) :=
    Space.second_measurable (traceSpace U) Y
  have appended : MeasurableMap (Space.product (traceSpace U) Y) (Space.list Y)
      (fun pair => pair.1.1 ++ [pair.2]) :=
    fun {set} => MeasurableMap.comp
      (before := fun (pair : (List α × U.Stat) × α) => (pair.1.1, pair.2))
      (append_last_measurable Y) (Space.pair_measurable draws drawn) (set := set)
  have incorporated : MeasurableMap (Space.product (traceSpace U) Y) U.statSpace
      (fun pair => U.incorporate pair.1.2 pair.2) :=
    fun {set} => MeasurableMap.comp
      (before := fun (pair : (List α × U.Stat) × α) => (pair.1.2, pair.2))
      U.incorporate_measurable (Space.pair_measurable statistic drawn) (set := set)
  exact fun {set} => Space.pair_measurable appended incorporated (set := set)

/-- One draw from the statistic, appended to the draws and incorporated. -/
@[expose] noncomputable def traceStep (U : Urn.{u, v} Y) (S : U.Sampled) :
    Kernel (traceSpace U) (traceSpace U) :=
  (Kernel.attach (S.kernel.precomp Prod.snd (Space.second_measurable (Space.list Y) U.statSpace))
      (S.kernelFinite.precomp _ (Space.second_measurable (Space.list Y) U.statSpace))).map
    (fun pair => (pair.1.1 ++ [pair.2], U.incorporate pair.1.2 pair.2))
    (trace_next_measurable U)

/-- The draws and the statistic after `n` more draws. -/
@[expose] noncomputable def traceLaw (U : Urn.{u, v} Y) (S : U.Sampled) (n : Nat) :
    Kernel (traceSpace U) (traceSpace U) :=
  Kernel.iterate (traceStep U S) n

end Urn

end

end Problib.Measure.Exchangeable
