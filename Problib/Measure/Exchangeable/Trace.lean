module

public import Problib.Measure.Exchangeable.Sampled
public import Problib.Measure.Kernel.Composition.Bind.Transport
public import Problib.Measure.Kernel.Product.Transport

set_option autoImplicit false

/-!
# The trace of a sampled urn

`traceLaw n` (Sampled.lean) runs `n` draws from a list of past draws and a
statistic, appending each draw and incorporating it. From the empty list and a
statistic `q`, the list it carries is a history drawn from `law q n`, and the
statistic it carries is that history's statistic from `q` (`law_trace`). So the
two descriptions of the first `n` observations agree: the history law, which
draws from the statistic of the history so far, and the trace, which carries
that statistic forward. Read for its statistic alone, the trace is the
statistic law (`traceLaw_stat`), so the history law's statistic is too
(`law_stat`).
-/

namespace Problib.Measure.Exchangeable

open Problib.Real

public section

universe u v

variable {α : Type u} {Y : Space α}

namespace Urn

variable {U : Urn.{u, v} Y}

/-- A history read as its list beside its statistic from `q`. -/
theorem trace_measurable (U : Urn.{u, v} Y) (q : U.Stat) (n : Nat) :
    MeasurableMap (historySpace Y n) (traceSpace U)
      (fun ys => (toList ys, U.stat q (toList ys))) :=
  Space.pair_measurable (toList_measurable Y n) (U.stat_measurable q n)

/-- One trace step from a state is the draw from its statistic, appended and
incorporated. -/
theorem traceStep_apply (S : U.Sampled) (h : List α) (s : U.Stat) :
    U.traceStep S (h, s) =
      (S.kernel s).map (fun y => (h ++ [y], U.incorporate s y))
        (MeasurableMap.comp (trace_next_measurable U)
          (Kernel.pair_left_measurable (source := traceSpace U) (target := Y) (h, s))) := by
  rw [traceStep, Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]
  rfl

/-- One statistic step from `s` is the draw from `s`, incorporated. -/
theorem statStep_apply (S : U.Sampled) (s : U.Stat) :
    U.statStep S s =
      (S.kernel s).map (fun y => U.incorporate s y)
        (MeasurableMap.comp U.incorporate_measurable
          (Kernel.pair_left_measurable (source := U.statSpace) (target := Y) s)) := by
  rw [statStep, Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]

/-- A statistic step keeps a valid statistic valid almost surely. -/
theorem statStep_valid_ae (S : U.Sampled) {s : U.Stat} (valid : S.Valid s) :
    (U.statStep S s).AE S.Valid := by
  rw [statStep_apply, Measure.ae_map_iff _ _ S.valid_measurable]
  exact S.valid_ae valid

/-- A trace step keeps a valid statistic valid almost surely. -/
theorem traceStep_valid_ae (S : U.Sampled) (h : List α) {s : U.Stat} (valid : S.Valid s) :
    (U.traceStep S (h, s)).AE fun trace => S.Valid trace.2 := by
  have validMeasurable : (traceSpace U).Measurable fun trace => S.Valid trace.2 :=
    Space.second_measurable (Space.list Y) U.statSpace S.valid_measurable
  rw [traceStep_apply]
  exact (Measure.ae_map_iff _ _ validMeasurable).mpr (S.valid_ae valid)

/-- From the empty list and `q`, the trace after `n` draws is a history from
`law q n`, read as its list beside its statistic. -/
theorem law_trace (S : U.Sampled) (q : U.Stat) (n : Nat) :
    (U.law S q n).map (fun ys => (toList ys, U.stat q (toList ys))) (trace_measurable U q n) =
      U.traceLaw S n ([], q) := by
  induction n with
  | zero =>
      rw [law_zero, Measure.map_dirac, traceLaw, Kernel.iterate_zero, Kernel.deterministic_apply,
        toList_empty]
      rfl
  | succ n induction =>
      rw [traceLaw, Kernel.iterate_succ_right, Kernel.comp_apply, ← traceLaw, ← induction,
        Measure.bind_map, law_succ, Measure.map_comp]
      unfold Measure.semiproduct
      rw [Measure.map_bind]
      refine congrArg (Measure.bind _) (Kernel.ext fun ys => ?_)
      rw [Kernel.map_apply, Kernel.precomp_apply, traceStep_apply]
      refine (Measure.map_comp (S.kernel (U.stat q (toList ys))) (fun value => (ys, value)) _
        (Kernel.pair_left_measurable (source := historySpace Y n) (target := Y) ys) _).trans ?_
      apply Measure.map_congr_function
      funext y
      rw [toList_snoc, stat_snoc]

/-- The statistic a trace carries after `n` draws has the statistic law from
the one it starts at, whatever draws it starts with. -/
theorem traceLaw_stat (S : U.Sampled) (n : Nat) (h : List α) (s : U.Stat) :
    (U.traceLaw S n (h, s)).map Prod.snd (Space.second_measurable (Space.list Y) U.statSpace) =
      U.statLaw S n s := by
  induction n with
  | zero =>
      rw [traceLaw, statLaw, Kernel.iterate_zero, Kernel.iterate_zero, Kernel.deterministic_apply,
        Kernel.deterministic_apply, Measure.map_dirac]
  | succ n induction =>
      rw [traceLaw, Kernel.iterate_succ_right, Kernel.comp_apply, ← traceLaw, Measure.map_bind,
        statLaw, Kernel.iterate_succ_right, Kernel.comp_apply, ← statLaw, ← induction,
        Measure.bind_map]
      refine congrArg (Measure.bind _) (Kernel.ext fun trace => ?_)
      obtain ⟨past, state⟩ := trace
      rw [Kernel.map_apply, Kernel.precomp_apply, traceStep_apply, statStep_apply]
      exact Measure.map_comp _ _ _ _ _

/-- From `q`, the statistic of a history from `law q n` has the statistic law
after `n` draws. -/
theorem law_stat (S : U.Sampled) (q : U.Stat) (n : Nat) :
    (U.law S q n).map (fun ys => U.stat q (toList ys)) (U.stat_measurable q n) =
      U.statLaw S n q := by
  rw [← traceLaw_stat S n [] q, ← law_trace, Measure.map_comp]

end Urn

end

end Problib.Measure.Exchangeable
