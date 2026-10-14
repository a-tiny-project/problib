module

public import Problib.Measure.Exchangeable.Density
public import Problib.Measure.Exchangeable.Power
public import Problib.Measure.Exchangeable.Witness

set_option autoImplicit false

/-!
# Deleting an observation

Forgetting the last draw of a sampled urn's history gives the history one
draw shorter (`Urn.law_delete_last`), because the draw kernel is a probability
law at every statistic the history almost surely reaches. Under
exchangeability any slot can be moved to the last one, so deleting any slot
of a view gives the shorter view (`Exchangeable.law_delete`). The proof uses
only the view's deletion laws `delete_view` and `delete_act`.
-/

namespace Problib.Measure.Exchangeable

open Problib.Real

public section

universe u v w

variable {α : Type u} {Y : Space α}

namespace Urn

variable {U : Urn.{u, v} Y}

/-- Forgetting the last of `n + 1` draws from a valid statistic gives the law of
the first `n` draws. -/
theorem law_delete_last (S : U.Sampled) (q : U.Stat) (valid : S.Valid q) (n : Nat) :
    (U.law S q (n + 1)).map (eraseAt (Fin.last n)) (eraseAt_measurable Y (Fin.last n)) =
      U.law S q n := by
  rw [law_succ, Measure.map_comp]
  have first : (fun pair : (Fin n → α) × α => eraseAt (Fin.last n) (snoc pair.1 pair.2)) =
      Prod.fst := by
    funext pair
    funext j
    change snoc pair.1 pair.2 (skip (Fin.last n) j) = pair.1 j
    rw [skip_last, snoc_castSucc]
  rw [map_congr_function _ first _ (Space.first_measurable (historySpace Y n) Y)]
  apply Measure.ext
  intro set measurable
  rw [Measure.map_apply _ _ _ measurable]
  have product : Set.preimage Prod.fst set = Set.product set (Set.univ : Set α) :=
    Set.ext fun _ => ⟨fun member => ⟨member, trivial⟩, fun member => member.1⟩
  rw [product]
  refine (Measure.semiproduct_apply_product (U.law S q n) (U.historyKernel S q n)
    (S.kernelFinite.precomp _ (U.stat_measurable q n)) measurable (Space.univ Y)).trans ?_
  have total : ((U.law S q n).restrict set).AEEq
      (fun ys => U.historyKernel S q n ys Set.univ) (fun _ => ENNReal.one) :=
    Measure.AE.mono ((law_valid S valid n).restrict set) fun ys statValid =>
      (S.markov statValid).univ_eq_one
  rw [Measure.lintegral_congr_ae total, Measure.lintegral_const, Measure.restrict_apply_univ,
    ENNReal.one_mul]

end Urn

/-- Under exchangeability, deleting any slot of a view of `n + 1` draws gives
the view of `n` draws. -/
theorem Exchangeable.law_delete {U : Urn.{u, v} Y} {S : U.Sampled} {W : View.{u, w} Y}
    (E : Exchangeable U S W) (n : Nat) (i : Fin (n + 1)) :
    ((U.law S U.init (n + 1)).map (W.view (n + 1)) (W.view_measurable (n + 1))).map
        (W.deleteView n i) (W.deleteView_measurable n i) =
      (U.law S U.init n).map (W.view n) (W.view_measurable n) := by
  let σ : Perm (n + 1) := (Perm.toLast i).symm
  have toLast : σ.inverse i = Fin.last n := Perm.toLast_forward_self i
  rw [← E.exchange (n + 1) σ, Measure.map_comp, Measure.map_comp,
    ← E.exchange n (σ.removeAt i),
    ← U.law_delete_last S U.init S.valid_init n, Measure.map_comp, Measure.map_comp]
  apply map_congr_function
  funext ys
  rw [W.delete_act, toLast, W.delete_view]

end

end Problib.Measure.Exchangeable
