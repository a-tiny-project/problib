module

public import Problib.Measure.Exchangeable.Urn
public import Problib.Measure.Exchangeable.Family
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Integral.Density.Change

set_option autoImplicit false

/-!
# Latent tables behind an urn

A latent presentation of an urn draws a table of values from a prior law at
each statistic, and scores each observation by a likelihood of the table
entries it reads. Its one obligation (`step`) is the urn's predictive: scoring
one observation under the prior at `s` gives the predictive's mass times the
prior at the incorporated statistic. Scoring a whole sequence then gives the
chain's mass times the prior at the final statistic (`collapse`).
-/

namespace Problib.Measure.Exchangeable

open Problib.Real

public section

universe u v

variable {α : Type u} {Y : Space α}

/-- A prior over tables of latent values and a likelihood of the entries each
observation reads, whose one-step posterior is the urn's predictive. -/
structure Urn.Latent (U : Urn.{u, v} Y) where
  Key : Type
  Value : Type
  valueSpace : Space Value
  Valid : U.Stat → Prop
  valid_init : Valid U.init
  valid_inc : ∀ {s} y, Valid s → Valid (U.incorporate s y)
  prior : LawFamily U.statSpace (Space.pi fun _ : Key => valueSpace)
  reads : α → List Key
  likelihood : α → List Value → ENNReal
  likelihood_measurable : ∀ y, ENNRealMeasurable (Space.pi fun _ : Key => valueSpace)
    fun table => likelihood y ((reads y).map table)
  step : ∀ {s} y, Valid s →
    (prior.kernel s).withDensity (fun table => likelihood y ((reads y).map table)) =
      Measure.smul (U.predictive s y) (prior.kernel (U.incorporate s y))

namespace Urn.Latent

variable {U : Urn.{u, v} Y} (L : U.Latent)

/-- The likelihood of a sequence of observations at a table. -/
@[expose] noncomputable def evidence : List α → (L.Key → L.Value) → ENNReal
  | [], _ => ENNReal.one
  | y :: ys, table => ENNReal.mul (L.likelihood y ((L.reads y).map table)) (evidence ys table)

theorem evidence_measurable : ∀ ys : List α,
    ENNRealMeasurable (Space.pi fun _ : L.Key => L.valueSpace) (L.evidence ys)
  | [] => ENNRealMeasurable.constant _ ENNReal.one
  | y :: ys => ENNRealMeasurable.mul (L.likelihood_measurable y) (evidence_measurable ys)

/-- The evidence does not depend on the order of the observations. -/
theorem evidence_perm {ys ys' : List α} (perm : ys.Perm ys') : L.evidence ys = L.evidence ys' := by
  induction perm with
  | nil => rfl
  | cons y _ induction =>
      funext table
      exact congrArg (ENNReal.mul _) (congrFun induction table)
  | swap y y' ys =>
      funext table
      change ENNReal.mul _ (ENNReal.mul _ _) = ENNReal.mul _ (ENNReal.mul _ _)
      rw [← ENNReal.mul_assoc, ← ENNReal.mul_assoc, ENNReal.mul_comm (L.likelihood y' _)]
  | trans _ _ first second => exact first.trans second

/-- A scaled measure weighted by a density is the weighted measure scaled. -/
theorem smul_withDensity_left {β : Type u} {space : Space β} (measure : Measure space)
    (factor : ENNReal) {density : β → ENNReal} (measurable : ENNRealMeasurable space density) :
    (Measure.smul factor measure).withDensity density =
      Measure.smul factor (measure.withDensity density) := by
  rw [← measure.withDensity_const, Measure.withDensity_withDensity _
    (ENNRealMeasurable.constant _ factor) measurable, Measure.smul_withDensity _ _ measurable]

/-- Scoring a sequence under the prior gives the chain's mass times the prior
at the final statistic. -/
theorem collapse : ∀ {q : U.Stat}, L.Valid q → ∀ ys : List α,
    (L.prior.kernel q).withDensity (L.evidence ys) =
      Measure.smul (U.chain q ys) (L.prior.kernel (U.stat q ys))
  | q, _, [] => by
      have one : L.evidence [] = fun _ => ENNReal.one := rfl
      rw [one, Measure.withDensity_one, U.chain_nil, U.stat_nil, Measure.one_smul]
  | q, valid, y :: ys => by
      have split : L.evidence (y :: ys) = fun table =>
          ENNReal.mul (L.likelihood y ((L.reads y).map table)) (L.evidence ys table) := rfl
      rw [split, ← Measure.withDensity_withDensity _ (L.likelihood_measurable y)
          (L.evidence_measurable ys), L.step y valid,
        smul_withDensity_left _ _ (L.evidence_measurable ys),
        collapse (L.valid_inc y valid) ys, Measure.smul_smul, U.chain_cons, U.stat_cons]

end Urn.Latent

end

end Problib.Measure.Exchangeable
