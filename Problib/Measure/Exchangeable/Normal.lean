module

public import Problib.Measure.Exchangeable.Sufficient
public import Problib.Analysis.Gaussian.Density

set_option autoImplicit false

/-!
# The Normal urn

Observations are Normal around an unknown mean with variance `likVar`, and the
mean is Normal with mean `priorMean` and variance `priorVar`. After `n`
observations with sum `t`, the next observation is Normal at the posterior
mean `postMean n t` with variance `postVar n + likVar`.

The urn keeps the raw history, and its measurable sets are the ones the count
and sum determine. Its predictive reads only the count and the sum, so "same
count, same sum" is sufficient (`normal_sufficient`).
-/

namespace Problib.Measure.Exchangeable

open Problib.Real Problib.Measure.Real Problib.Real.Construction.Dedekind

public section

noncomputable section

namespace Normal

/-- The sum of a history. -/
@[expose] def total (s : List Carrier) : Carrier := s.foldl add zero

theorem total_snoc (s : List Carrier) (y : Carrier) : total (s ++ [y]) = add (total s) y :=
  List.foldl_append

/-- The count and the sum of a history. -/
@[expose] def summary (s : List Carrier) : Nat × Carrier := (s.length, total s)

/-- Histories, measured through their count and sum. -/
@[expose] def statSpace : Space (List Carrier) :=
  Space.comap summary (Space.product (Space.discrete Nat) borel)

/-- The posterior variance of the mean after `n` observations. -/
@[expose] def postVar (priorVar likVar : Carrier) (n : Nat) : Carrier :=
  inverse (add (inverse priorVar) (div (selection.ofRat n) likVar))

/-- The posterior mean after `n` observations with sum `t`. -/
@[expose] def postMean (priorMean priorVar likVar : Carrier) (n : Nat) (t : Carrier) : Carrier :=
  mul (postVar priorVar likVar n) (add (div priorMean priorVar) (div t likVar))

theorem count_measurable :
    MeasurableMap (Space.product statSpace borel) (Space.discrete Nat) fun pair => pair.1.length :=
  MeasurableMap.comp (Space.first_measurable _ _)
    (MeasurableMap.comp (Space.comap_map summary _) (Space.first_measurable _ _))

theorem total_measurable :
    MeasurableMap (Space.product statSpace borel) borel fun pair => total pair.1 :=
  MeasurableMap.comp (Space.second_measurable _ _)
    (MeasurableMap.comp (Space.comap_map summary _) (Space.first_measurable _ _))

/-- Appending an observation is measurable on summarized histories. -/
theorem incorporate_measurable :
    MeasurableMap (Space.product statSpace borel) statSpace
      fun pair : List Carrier × Carrier => pair.1 ++ [pair.2] := by
  intro region regionMeasurable
  obtain ⟨target, targetMeasurable, rfl⟩ :=
    (Space.comap_measurable_iff summary _ region).mp regionMeasurable
  have equal : (fun pair : List Carrier × Carrier => summary (pair.1 ++ [pair.2])) =
      fun pair => (pair.1.length + 1, add (total pair.1) pair.2) := by
    funext pair
    rw [summary, List.length_append, total_snoc]
    rfl
  change (Space.product statSpace borel).Measurable
    (Set.preimage (fun pair : List Carrier × Carrier => summary (pair.1 ++ [pair.2])) target)
  rw [equal]
  exact Space.pair_measurable
    (MeasurableMap.comp (MeasurableMap.from_discrete _ fun n : Nat => n + 1) count_measurable)
    (measurable_add total_measurable (Space.second_measurable _ _)) targetMeasurable

/-- The predictive density reads a measurable count and sum. -/
theorem predictive_measurable (priorMean priorVar likVar : Carrier) :
    ENNRealMeasurable (Space.product statSpace borel) fun pair : List Carrier × Carrier =>
      ENNReal.finite (Analysis.Gaussian.density
        (postMean priorMean priorVar likVar pair.1.length (total pair.1))
        (add (postVar priorVar likVar pair.1.length) likVar) pair.2) := by
  have mean : MeasurableMap (Space.product statSpace borel) borel
      fun pair : List Carrier × Carrier =>
        postMean priorMean priorVar likVar pair.1.length (total pair.1) := by
    unfold postMean
    exact measurable_mul
      (left := fun pair : List Carrier × Carrier => postVar priorVar likVar pair.1.length)
      (right := fun pair => add (div priorMean priorVar) (div (total pair.1) likVar))
      (MeasurableMap.comp (MeasurableMap.from_discrete borel (postVar priorVar likVar))
        count_measurable)
      (measurable_add (left := fun _ => div priorMean priorVar)
        (right := fun pair : List Carrier × Carrier => div (total pair.1) likVar)
        (MeasurableMap.constant _ borel _)
        (measurable_div (left := fun pair : List Carrier × Carrier => total pair.1)
          (right := fun _ => likVar) total_measurable (MeasurableMap.constant _ borel likVar)))
  have variance : MeasurableMap (Space.product statSpace borel) borel
      fun pair : List Carrier × Carrier => add (postVar priorVar likVar pair.1.length) likVar :=
    MeasurableMap.comp
      (MeasurableMap.from_discrete borel fun n => add (postVar priorVar likVar n) likVar)
      count_measurable
  exact ENNRealMeasurable.comp
    (map := fun p : (Carrier × Carrier) × Carrier =>
      ENNReal.finite (Analysis.Gaussian.density p.1.1 p.1.2 p.2))
    (before := fun pair : List Carrier × Carrier =>
      ((postMean priorMean priorVar likVar pair.1.length (total pair.1),
        add (postVar priorVar likVar pair.1.length) likVar), pair.2))
    Analysis.Gaussian.density_measurable
    (Space.pair_measurable (Space.pair_measurable mean variance) (Space.second_measurable _ _))

end Normal

open Normal

/-- The Normal–Normal urn with fixed variances. Its statistic is the raw
history. -/
@[expose] def normalUrn (priorMean priorVar likVar : Carrier) : Urn.{0, 0} borel where
  Stat := List Carrier
  statSpace := Normal.statSpace
  init := []
  incorporate := fun s y => s ++ [y]
  predictive := fun s y => ENNReal.finite (Analysis.Gaussian.density
    (postMean priorMean priorVar likVar s.length (total s))
    (add (postVar priorVar likVar s.length) likVar) y)
  incorporate_measurable := Normal.incorporate_measurable
  predictive_measurable := Normal.predictive_measurable priorMean priorVar likVar

/-- Histories with the same count and sum predict alike and stay so: the
Normal urn passes `Sufficient`. -/
theorem normal_sufficient (priorMean priorVar likVar : Carrier) :
    Sufficient (normalUrn priorMean priorVar likVar)
      fun (s s' : List Carrier) => s.length = s'.length ∧ total s = total s' := by
  intro (s : List Carrier) (s' : List Carrier) ⟨length, sum⟩
  refine ⟨fun y => ?_, fun y => ?_⟩
  · change ENNReal.finite _ = ENNReal.finite _
    rw [length, sum]
  · change (s ++ [y]).length = (s' ++ [y]).length ∧ total (s ++ [y]) = total (s' ++ [y])
    rw [List.length_append, List.length_append, length, total_snoc, total_snoc, sum]
    exact ⟨rfl, rfl⟩

end

end

end Problib.Measure.Exchangeable
