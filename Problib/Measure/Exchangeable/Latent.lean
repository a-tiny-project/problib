module

public import Problib.Measure.Exchangeable.Urn
public import Problib.Measure.Exchangeable.Family
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Kernel.FoldList
public import Problib.Measure.Integral.Lebesgue.Extensionality
public import Problib.Measure.Integral.Lebesgue.Transport

set_option autoImplicit false

/-!
# Latent tables behind an urn

A latent presentation of an urn draws a table of values from a prior law at
each statistic, and scores each observation by a likelihood of the table
entries it reads. Its one obligation (`step`) is the urn's predictive: scoring
one observation under the prior at `s` gives the predictive's mass times the
prior at the incorporated statistic. Scoring a whole sequence then gives the
chain's mass times the prior at the final statistic (`collapse`), so the chain
does not depend on the order of the observations (`chain_perm`).
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

/-- The kernel that keeps its input and weights it by a density. -/
noncomputable def weight {β : Type u} {space : Space β} (density : β → ENNReal)
    (measurable : ENNRealMeasurable space density) : Measure.Kernel space space where
  toFun value := (Measure.dirac space value).withDensity density
  measurable := by
    intro set setMeasurable
    have equal : (fun value => (Measure.dirac space value).withDensity density set) =
        ennrealIndicator set density := by
      funext value
      rw [Measure.withDensity_apply _ _ setMeasurable, ← lintegral_indicator _ _ setMeasurable,
        lintegral_dirac _ _ (measurable.indicator setMeasurable)]
    rw [equal]
    exact measurable.indicator setMeasurable

/-- Binding a measure with a weight kernel weights the measure. -/
theorem bind_weight {β : Type u} {space : Space β} (measure : Measure space)
    {density : β → ENNReal} (measurable : ENNRealMeasurable space density) :
    measure.bind (weight density measurable) = measure.withDensity density := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun integrand integrandMeasurable => ?_
  rw [Measure.lintegral_bind _ _ integrandMeasurable,
    lintegral_withDensity _ measurable integrandMeasurable]
  apply lintegral_congr
  intro value
  change lintegral ((Measure.dirac space value).withDensity density) integrand = _
  rw [lintegral_withDensity _ measurable integrandMeasurable,
    lintegral_dirac _ _ (measurable.mul integrandMeasurable)]

/-- Weighting by one density and then another weights by their product. -/
theorem weight_comp {β : Type u} {space : Space β} {first second : β → ENNReal}
    (firstMeasurable : ENNRealMeasurable space first)
    (secondMeasurable : ENNRealMeasurable space second) :
    (weight first firstMeasurable).comp (weight second secondMeasurable) =
      weight (fun value => ENNReal.mul (first value) (second value))
        (firstMeasurable.mul secondMeasurable) := by
  apply Measure.Kernel.ext
  intro value
  rw [Measure.Kernel.comp_apply, bind_weight]
  exact Measure.withDensity_withDensity _ firstMeasurable secondMeasurable

/-- Scoring a sequence under the prior gives the chain's mass times the prior
at the final statistic. -/
theorem collapse : ∀ {q : U.Stat}, L.Valid q → ∀ ys : List α,
    (L.prior.kernel q).withDensity (L.evidence ys) =
      Measure.smul (U.chain q ys) (L.prior.kernel (U.stat q ys)) := by
  intro q valid ys
  rw [← bind_weight _ (L.evidence_measurable ys)]
  refine Measure.Kernel.bind_of_summarizes (relate := fun s => L.prior.kernel s)
    (step := fun y => weight _ (L.likelihood_measurable y))
    (run := fun ys => weight _ (L.evidence_measurable ys))
    ⟨fun _ y holds => L.valid_inc y holds, fun _ y holds => ?_⟩ ?_ (fun y ys => ?_)
    U.chain_nil U.chain_cons U.stat_nil U.stat_cons ys valid
  · rw [bind_weight]
    exact L.step y holds
  · apply Measure.Kernel.ext
    intro table
    exact Measure.withDensity_one _
  · exact (weight_comp (L.likelihood_measurable y) (L.evidence_measurable ys)).symm

/-- At a valid statistic the chain does not depend on the order of the
observations: it is the scored prior's total mass. -/
theorem chain_perm {q : U.Stat} (valid : L.Valid q) {ys ys' : List α} (perm : ys.Perm ys') :
    U.chain q ys = U.chain q ys' := by
  have total : ∀ zs, U.chain q zs = (L.prior.kernel q).withDensity (L.evidence zs) Set.univ :=
    fun zs => by
      rw [L.collapse valid zs, Measure.smul_apply_measurable _ _ (Space.univ _),
        (L.prior.markov _).univ_eq_one, ENNReal.mul_one]
  rw [total ys, total ys', L.evidence_perm perm]

end Urn.Latent

end

end Problib.Measure.Exchangeable
