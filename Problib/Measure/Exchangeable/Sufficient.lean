module

public import Problib.Measure.Exchangeable.Urn

set_option autoImplicit false

/-!
# Sufficient relations

A relation on an urn's statistics is sufficient when related statistics
predict every next observation alike and stay related after it. Related
statistics then reach related statistics along any sequence (`stat_rel`) and
give every sequence the same density (`chain_eq`). So an urn may keep any
statistic in a class: the Normal urn keeps its raw history, and only the count
and the sum of the history matter.
-/

namespace Problib.Measure.Exchangeable

public section

universe u v

variable {α : Type u} {Y : Space α}

/-- Related statistics predict alike and stay related after any observation. -/
@[expose] def Sufficient (U : Urn.{u, v} Y) (rel : U.Stat → U.Stat → Prop) : Prop :=
  ∀ s s', rel s s' →
    (∀ y, U.predictive s y = U.predictive s' y) ∧ ∀ y, rel (U.incorporate s y) (U.incorporate s' y)

namespace Sufficient

variable {U : Urn.{u, v} Y} {rel : U.Stat → U.Stat → Prop}

/-- Related statistics stay related along any sequence. -/
theorem stat_rel (sufficient : Sufficient U rel) {q q' : U.Stat} (related : rel q q')
    (ys : List α) : rel (U.stat q ys) (U.stat q' ys) := by
  induction ys generalizing q q' with
  | nil => exact related
  | cons y ys induction => exact induction ((sufficient q q' related).2 y)

/-- Related statistics give every sequence the same density. -/
theorem chain_eq (sufficient : Sufficient U rel) {q q' : U.Stat} (related : rel q q')
    (ys : List α) : U.chain q ys = U.chain q' ys := by
  induction ys generalizing q q' with
  | nil => rfl
  | cons y ys induction =>
      rw [Urn.chain_cons, Urn.chain_cons, (sufficient q q' related).1 y,
        induction ((sufficient q q' related).2 y)]

end Sufficient

end

end Problib.Measure.Exchangeable
