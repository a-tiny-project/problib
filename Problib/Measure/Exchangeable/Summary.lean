module

public import Problib.Measure.Exchangeable.Keyed
public import Problib.Measure.Exchangeable.Sufficient

set_option autoImplicit false

/-!
# Urns on a summary of their statistic

A summary of an urn's statistic carries everything its predictive and its
incorporation read: the predictive at a statistic is a function of the
statistic's summary, and incorporating an observation moves the summary by a
map on summaries. The urn then runs on the summaries (`Urn.ofSummary`). Its
statistic after a sequence is the summary of the original's
(`ofSummary_stat`), so the two urns give every sequence the same density
(`ofSummary_chain`). Statistics with one summary are `Sufficient`
(`ofSummary_sufficient`). A local latent presentation whose prior reads only
the summary is one of the summary urn (`LocalLatent.ofSummary`).
-/

namespace Problib.Measure.Exchangeable

open Problib.Real

public section

universe u v

variable {α : Type u} {Y : Space α}

/-- A measurable summary of an urn's statistic that its predictive and its
incorporation factor through. -/
structure Urn.Summary (U : Urn.{u, v} Y) where
  Value : Type
  space : Space Value
  summary : U.Stat → Value
  summary_measurable : MeasurableMap U.statSpace space summary
  predictive : Value → α → ENNReal
  predictive_eq : ∀ s y, U.predictive s y = predictive (summary s) y
  predictive_measurable : ENNRealMeasurable (Space.product space Y) fun pair => predictive pair.1 pair.2
  incorporate : Value → α → Value
  incorporate_eq : ∀ s y, summary (U.incorporate s y) = incorporate (summary s) y
  incorporate_measurable :
    MeasurableMap (Space.product space Y) space fun pair => incorporate pair.1 pair.2

namespace Urn

variable {U : Urn.{u, v} Y} (S : U.Summary)

/-- The urn on the summaries. -/
@[expose] def ofSummary : Urn.{u, 0} Y where
  Stat := S.Value
  statSpace := S.space
  init := S.summary U.init
  incorporate := S.incorporate
  predictive := S.predictive
  incorporate_measurable := S.incorporate_measurable
  predictive_measurable := S.predictive_measurable

/-- The summary urn's statistic after a sequence is the summary of the
original's. -/
theorem ofSummary_stat (q : U.Stat) (ys : List α) :
    (ofSummary S).stat (S.summary q) ys = S.summary (U.stat q ys) := by
  induction ys generalizing q with
  | nil => rfl
  | cons y ys induction =>
      change (ofSummary S).stat (S.incorporate (S.summary q) y) ys = _
      rw [← S.incorporate_eq, induction]
      rfl

/-- The summary urn gives every sequence the original's density. -/
theorem ofSummary_chain (q : U.Stat) (ys : List α) :
    (ofSummary S).chain (S.summary q) ys = U.chain q ys := by
  induction ys generalizing q with
  | nil => rfl
  | cons y ys induction =>
      change ENNReal.mul (S.predictive (S.summary q) y)
        ((ofSummary S).chain (S.incorporate (S.summary q) y) ys) = _
      rw [← S.incorporate_eq, induction, ← S.predictive_eq]
      rfl

/-- Statistics with one summary are sufficient. -/
theorem ofSummary_sufficient : Sufficient U fun s s' => S.summary s = S.summary s' :=
  fun s s' same => by
    have same : S.summary s = S.summary s' := same
    exact ⟨fun y => by rw [S.predictive_eq, S.predictive_eq, same],
      fun y => by
        show S.summary (U.incorporate s y) = S.summary (U.incorporate s' y)
        rw [S.incorporate_eq, S.incorporate_eq, same]⟩

/-- A local latent presentation whose prior reads only the summary is one of
the summary urn. Its valid summaries are the summaries of valid statistics. -/
@[expose] def LocalLatent.ofSummary (L : U.LocalLatent) (prior : LawFamily S.space L.valueSpace)
    (prior_eq : ∀ s, L.prior.kernel s = prior.kernel (S.summary s)) :
    (Urn.ofSummary S).LocalLatent where
  Value := L.Value
  valueSpace := L.valueSpace
  standard := L.standard
  Valid := fun summary => ∃ s, L.Valid s ∧ S.summary s = summary
  valid_init := ⟨U.init, L.valid_init, rfl⟩
  valid_inc := fun y ⟨s, valid, same⟩ =>
    ⟨U.incorporate s y, L.valid_inc y valid, by rw [S.incorporate_eq, same]; rfl⟩
  prior := prior
  likelihood := L.likelihood
  likelihood_measurable := L.likelihood_measurable
  step := fun y ⟨s, valid, same⟩ => by
    subst same
    change (prior.kernel (S.summary s)).withDensity (L.likelihood y) =
      Measure.smul (S.predictive (S.summary s) y) (prior.kernel (S.incorporate (S.summary s) y))
    rw [← prior_eq, ← S.predictive_eq, ← S.incorporate_eq, ← prior_eq]
    exact L.step y valid

end Urn

end

end Problib.Measure.Exchangeable
