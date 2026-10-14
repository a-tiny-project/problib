module

public import Problib.Measure.Exchangeable.History

set_option autoImplicit false

/-!
# Views of a history

A view reads a statistic of each history that permutations act on
(`equivariant`) and that a deletion map carries from `n + 1` slots to `n`
(`delete_view`). `delete_act` says how deletion commutes with the action: it
deletes slot `σ⁻¹ i` before σ acts and slot `i` after, so the permutation that
remains is `σ.removeAt i`. `View.raw` reads the history itself.
-/

namespace Problib.Measure.Exchangeable

public section

universe u w

variable {α : Type u}

/-- An equivariant, deletable statistic of histories. -/
structure View (Y : Space α) where
  V : Nat → Type w
  space : (n : Nat) → Space (V n)
  view : (n : Nat) → (Fin n → α) → V n
  view_measurable : ∀ n, MeasurableMap (historySpace Y n) (space n) (view n)
  act : (n : Nat) → Perm n → V n → V n
  act_measurable : ∀ n σ, MeasurableMap (space n) (space n) (act n σ)
  equivariant : ∀ n σ ys, view n (permute σ ys) = act n σ (view n ys)
  deleteView : (n : Nat) → Fin (n + 1) → V (n + 1) → V n
  deleteView_measurable : ∀ n i, MeasurableMap (space (n + 1)) (space n) (deleteView n i)
  delete_view : ∀ n i ys, deleteView n i (view (n + 1) ys) = view n (eraseAt i ys)
  delete_act : ∀ n (σ : Perm (n + 1)) i v,
    deleteView n i (act (n + 1) σ v) = act n (σ.removeAt i) (deleteView n (σ.inverse i) v)

/-- The view that reads the whole history. -/
@[expose] def View.raw (Y : Space α) : View.{u, u} Y where
  V n := Fin n → α
  space n := historySpace Y n
  view _ ys := ys
  view_measurable n := MeasurableMap.identity (historySpace Y n)
  act _ σ := permute σ
  act_measurable n σ := permute_measurable Y σ
  equivariant _ _ _ := rfl
  deleteView _ i := eraseAt i
  deleteView_measurable n i := eraseAt_measurable Y i
  delete_view _ _ _ := rfl
  delete_act _ σ i ys := by
    funext j
    change ys (σ.inverse (skip i j)) = ys (skip (σ.inverse i) ((σ.removeAt i).inverse j))
    rw [Perm.removeAt_spec]

end

end Problib.Measure.Exchangeable
