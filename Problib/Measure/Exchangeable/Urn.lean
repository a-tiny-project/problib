module

public import Problib.Measure.Exchangeable.History

set_option autoImplicit false

/-!
# Urns

An urn keeps a statistic of the observations so far. `incorporate` adds one
observation to it, and `predictive s y` is the density of the next observation
`y` at statistic `s`. `stat q ys` is the statistic after the observations `ys`
from `q`, and `chain q ys` is the product of the predictives along the prefixes
of `ys`, the density of the whole sequence.
-/

namespace Problib.Measure.Exchangeable

open Problib.Real

public section

universe u v

variable {α : Type u}

/-- A sequential predictive: a measurable statistic of the past and the density
of the next observation at each statistic. -/
structure Urn (Y : Space α) where
  Stat : Type v
  statSpace : Space Stat
  init : Stat
  incorporate : Stat → α → Stat
  predictive : Stat → α → ENNReal
  incorporate_measurable :
    MeasurableMap (Space.product statSpace Y) statSpace fun pair => incorporate pair.1 pair.2
  predictive_measurable :
    ENNRealMeasurable (Space.product statSpace Y) fun pair => predictive pair.1 pair.2

namespace Urn

variable {Y : Space α} (U : Urn.{u, v} Y)

/-- The statistic after the observations `ys` from `q`, first observation first. -/
@[expose] def stat (q : U.Stat) (ys : List α) : U.Stat :=
  ys.foldl U.incorporate q

/-- The product of the predictives of `ys` along its prefixes from `q`. -/
@[expose] noncomputable def chain : U.Stat → List α → ENNReal
  | _, [] => ENNReal.one
  | q, y :: ys => ENNReal.mul (U.predictive q y) (chain (U.incorporate q y) ys)

theorem stat_nil (q : U.Stat) : U.stat q [] = q := rfl

theorem stat_cons (q : U.Stat) (y : α) (ys : List α) :
    U.stat q (y :: ys) = U.stat (U.incorporate q y) ys := rfl

theorem stat_append (q : U.Stat) (xs ys : List α) :
    U.stat q (xs ++ ys) = U.stat (U.stat q xs) ys :=
  List.foldl_append

theorem stat_snoc (q : U.Stat) (ys : List α) (y : α) :
    U.stat q (ys ++ [y]) = U.incorporate (U.stat q ys) y := by
  rw [stat_append]
  rfl

theorem chain_nil (q : U.Stat) : U.chain q [] = ENNReal.one := rfl

theorem chain_cons (q : U.Stat) (y : α) (ys : List α) :
    U.chain q (y :: ys) = ENNReal.mul (U.predictive q y) (U.chain (U.incorporate q y) ys) :=
  rfl

theorem chain_append (q : U.Stat) (xs ys : List α) :
    U.chain q (xs ++ ys) = ENNReal.mul (U.chain q xs) (U.chain (U.stat q xs) ys) := by
  induction xs generalizing q with
  | nil => exact (ENNReal.one_mul _).symm
  | cons x xs induction =>
      simp only [List.cons_append, chain_cons, stat_cons, induction, ENNReal.mul_assoc]

theorem chain_snoc (q : U.Stat) (ys : List α) (y : α) :
    U.chain q (ys ++ [y]) = ENNReal.mul (U.chain q ys) (U.predictive (U.stat q ys) y) := by
  rw [chain_append, chain_cons, chain_nil, ENNReal.mul_one]

/-- The statistic of a history is measurable in the history. -/
theorem stat_measurable (q : U.Stat) (n : Nat) :
    MeasurableMap (historySpace Y n) U.statSpace (fun ys => U.stat q (toList ys)) := by
  induction n with
  | zero =>
      have equal : (fun ys : Fin 0 → α => U.stat q (toList ys)) = fun _ => q := by
        funext ys
        rw [toList_empty, stat_nil]
      rw [equal]
      exact fun {set} => MeasurableMap.constant (historySpace Y 0) U.statSpace q (set := set)
  | succ n induction =>
      have equal : (fun ys : Fin (n + 1) → α => U.stat q (toList ys)) =
          fun ys => U.incorporate (U.stat q (toList fun index => ys index.castSucc))
            (ys (Fin.last n)) := by
        funext ys
        unfold toList
        rw [List.ofFn_succ_last, stat_snoc]
      rw [equal]
      have initial : MeasurableMap (historySpace Y (n + 1)) (historySpace Y n)
          (fun ys index => ys index.castSucc) :=
        Space.pi_reindex (fun _ => Y) Fin.castSucc
      have previous : MeasurableMap (historySpace Y (n + 1)) U.statSpace
          (fun ys => U.stat q (toList fun index => ys index.castSucc)) :=
        MeasurableMap.comp (before := fun (ys : Fin (n + 1) → α) index => ys index.castSucc)
          induction initial
      have last : MeasurableMap (historySpace Y (n + 1)) Y (fun ys => ys (Fin.last n)) :=
        Space.coordinate_measurable (fun _ => Y) (Fin.last n)
      have paired : MeasurableMap (historySpace Y (n + 1)) (Space.product U.statSpace Y)
          (fun ys => (U.stat q (toList fun index => ys index.castSucc), ys (Fin.last n))) :=
        Space.pair_measurable previous last
      exact fun {set} => MeasurableMap.comp
        (before := fun (ys : Fin (n + 1) → α) =>
          (U.stat q (toList fun index => ys index.castSucc), ys (Fin.last n)))
        U.incorporate_measurable paired (set := set)

/-- The predictive at a fixed statistic is measurable in the observation. -/
theorem predictive_at_measurable (s : U.Stat) :
    ENNRealMeasurable Y (U.predictive s) := by
  have paired : MeasurableMap Y (Space.product U.statSpace Y) (fun y => (s, y)) :=
    Space.pair_measurable (MeasurableMap.constant Y U.statSpace s) (MeasurableMap.identity Y)
  exact ENNRealMeasurable.comp (before := fun (y : α) => (s, y)) U.predictive_measurable paired

end Urn

end

end Problib.Measure.Exchangeable
