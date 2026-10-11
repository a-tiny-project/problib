module

public import Problib.Measure.Exchangeable.History
public import Problib.Measure.Kernel.Product.Transport
public import Problib.Measure.Kernel.Product

set_option autoImplicit false

/-!
# Permutation invariance of product powers

`insertAt j y h` places `y` in slot `j` and the history `h` in order around it.
Inserting an independent draw from the base at any slot of the `n`-fold power
gives the `(n + 1)`-fold power (`power_insertAt`): at the last slot this is the
definition, and an earlier slot moves past the last draw by the symmetry of
the product of two base factors. A permuted history with one more observation
is a permuted history with that observation inserted where the permutation
sends the last slot (`permute_snoc`). So every permutation leaves each power
unchanged (`power_permute`).
-/

namespace Problib.Measure.Exchangeable

open Problib.Real

public section

universe u v w

variable {α : Type u} {n : Nat}

/-- The history with `y` in slot `j` and `h` in order in the other slots. -/
@[expose] def insertAt (j : Fin (n + 1)) (y : α) (h : Fin n → α) : Fin (n + 1) → α :=
  fun index => if same : index = j then y else h (unskip j index same)

theorem insertAt_measurable (Y : Space α) (j : Fin (n + 1)) :
    MeasurableMap (Space.product (historySpace Y n) Y) (historySpace Y (n + 1))
      (fun pair => insertAt j pair.2 pair.1) := by
  apply Space.pi_measurable
  intro index
  by_cases same : index = j
  · have equal : (fun pair : (Fin n → α) × α => insertAt j pair.2 pair.1 index) =
        (fun pair => pair.2) := by
      funext pair
      simp [insertAt, same]
    rw [equal]
    exact Space.second_measurable _ _
  · have equal : (fun pair : (Fin n → α) × α => insertAt j pair.2 pair.1 index) =
        (fun pair => pair.1 (unskip j index same)) := by
      funext pair
      simp [insertAt, same]
    rw [equal]
    exact MeasurableMap.comp (Space.coordinate_measurable (fun _ => Y) _)
      (Space.first_measurable _ _)

theorem insertAt_self (j : Fin (n + 1)) (y : α) (h : Fin n → α) : insertAt j y h j = y := by
  simp [insertAt]

theorem insertAt_skip (j : Fin (n + 1)) (y : α) (h : Fin n → α) (k : Fin n) :
    insertAt j y h (skip j k) = h k := by
  simp only [insertAt, skip_ne j k, dite_false, unskip_skip]

/-- Every slot is `j` or a slot other than `j`. -/
theorem eq_or_skip (j index : Fin (n + 1)) : index = j ∨ ∃ k, index = skip j k := by
  by_cases same : index = j
  · exact Or.inl same
  · exact Or.inr ⟨unskip j index same, (skip_unskip j index same).symm⟩

theorem skip_last (k : Fin n) : skip (Fin.last n) k = k.castSucc :=
  Fin.ext (by rw [skip_val]; simp [k.isLt])

theorem castSucc_skip {m : Nat} (j : Fin (m + 1)) (k : Fin m) :
    (skip j k).castSucc = skip j.castSucc k.castSucc := by
  apply Fin.ext
  rw [Fin.val_castSucc, skip_val, skip_val]
  rfl

theorem skip_castSucc_last {m : Nat} (j : Fin (m + 1)) :
    skip j.castSucc (Fin.last m) = Fin.last (m + 1) := by
  have := j.isLt
  apply Fin.ext
  rw [skip_val]
  simp only [Fin.val_last, Fin.val_castSucc]
  split <;> omega

/-- Inserting at the last slot appends. -/
theorem insertAt_last (y : α) (h : Fin n → α) : insertAt (Fin.last n) y h = snoc h y := by
  funext index
  induction index using Fin.lastCases with
  | last => rw [insertAt_self, snoc_last]
  | cast k => rw [← skip_last, insertAt_skip, skip_last, snoc_castSucc]

/-- Inserting before the last slot commutes with appending. -/
theorem insertAt_snoc {m : Nat} (j : Fin (m + 1)) (y y' : α) (h : Fin m → α) :
    insertAt j.castSucc y (snoc h y') = snoc (insertAt j y h) y' := by
  funext index
  induction index using Fin.lastCases with
  | last => rw [snoc_last, ← skip_castSucc_last j, insertAt_skip, snoc_last]
  | cast k =>
      rw [snoc_castSucc]
      rcases eq_or_skip j k with same | ⟨other, rfl⟩
      · subst same
        rw [insertAt_self, insertAt_self]
      · rw [castSucc_skip, insertAt_skip, snoc_castSucc, insertAt_skip]

/-- A permuted history with one more observation is the permuted history with
the observation inserted where the permutation sends the last slot. -/
theorem permute_snoc (σ : Perm (n + 1)) (h : Fin n → α) (y : α) :
    permute σ (snoc h y) =
      insertAt (σ.forward (Fin.last n)) y (permute (σ.removeAt (σ.forward (Fin.last n))) h) := by
  funext index
  rcases eq_or_skip (σ.forward (Fin.last n)) index with same | ⟨k, rfl⟩
  · subst same
    simp only [permute, σ.inverse_forward, snoc_last, insertAt_self]
  · simp only [permute, insertAt_skip]
    rw [← Perm.removeAt_spec, σ.inverse_forward, skip_last, snoc_castSucc]

theorem map_congr_function {β : Type v} {γ : Type w} {source : Space β}
    (measure : Measure source)
    {first second : β → γ} {Z : Space γ} (equal : first = second)
    (firstMeasurable : MeasurableMap source Z first)
    (secondMeasurable : MeasurableMap source Z second) :
    measure.map first firstMeasurable = measure.map second secondMeasurable := by
  subst equal
  rfl

/-- Swapping the last two of three product factors leaves a product with two
equal base factors unchanged. -/
theorem prod_swap_last {β : Type u} {Y : Space α} {source : Space β} (left : Measure source)
    (base : Measure Y) (finite : Measure.SFinite base)
    (swapMeasurable : MeasurableMap (Space.product (Space.product source Y) Y)
      (Space.product (Space.product source Y) Y)
      (fun value => ((value.1.1, value.2), value.1.2))) :
    (Measure.prod (Measure.prod left base finite) base finite).map
        (fun value => ((value.1.1, value.2), value.1.2)) swapMeasurable =
      Measure.prod (Measure.prod left base finite) base finite := by
  let pairs := Measure.prod base base finite
  let pairsFinite : Measure.SFinite pairs := Measure.SFinite.prod finite finite
  have regroup : MeasurableMap (Space.product source (Space.product Y Y))
      (Space.product (Space.product source Y) Y)
      (fun value => ((value.1, value.2.1), value.2.2)) :=
    Space.unassociate_measurable source Y Y
  have inner : MeasurableMap (Space.product source (Space.product Y Y))
      (Space.product source (Space.product Y Y)) (fun value => (value.1, (value.2.2, value.2.1))) :=
    Space.product_map (MeasurableMap.identity source) (Space.swap_measurable Y Y)
  have swapped :
      pairs.map (fun value : α × α => (value.2, value.1)) (Space.swap_measurable Y Y) =
      pairs := Measure.prod_swap finite finite
  rw [Measure.prod_associate left base base finite finite]
  calc ((Measure.prod left pairs pairsFinite).map
          (fun value => ((value.1, value.2.1), value.2.2)) regroup).map
        (fun value => ((value.1.1, value.2), value.1.2)) swapMeasurable
      = ((Measure.prod left pairs pairsFinite).map
          (fun value => (value.1, (value.2.2, value.2.1))) inner).map
          (fun value => ((value.1, value.2.1), value.2.2)) regroup := by
        rw [Measure.map_comp, Measure.map_comp]
    _ = (Measure.prod left (pairs.map (fun value : α × α => (value.2, value.1))
          (Space.swap_measurable Y Y)) (pairsFinite.map _ (Space.swap_measurable Y Y))).map
          (fun value => ((value.1, value.2.1), value.2.2)) regroup := by
        rw [Measure.prod_map_right left pairs pairsFinite _ (Space.swap_measurable Y Y)]
    _ = (Measure.prod left pairs pairsFinite).map
          (fun value => ((value.1, value.2.1), value.2.2)) regroup := by
        rw [Measure.prod_congr_right left _ pairsFinite swapped]

/-- Inserting an independent draw from the base at any slot of the `n`-fold
power gives the `(n + 1)`-fold power. -/
theorem power_insertAt {Y : Space α} (base : Measure Y) (finite : Measure.SFinite base) :
    ∀ (n : Nat) (j : Fin (n + 1)),
      (Measure.prod (power base finite n) base finite).map
          (fun pair => insertAt j pair.2 pair.1) (insertAt_measurable Y j) =
        power base finite (n + 1)
  | 0, j => by
      have atLast : j = Fin.last 0 := Fin.ext (by have := j.isLt; simp)
      subst atLast
      exact (map_congr_function _
        (funext fun (pair : (Fin 0 → α) × α) => insertAt_last pair.2 pair.1) _ _).trans
        (power_succ base finite 0).symm
  | m + 1, j => by
      by_cases atLast : j = Fin.last (m + 1)
      · subst atLast
        exact (map_congr_function _
          (funext fun (pair : (Fin (m + 1) → α) × α) => insertAt_last pair.2 pair.1) _ _).trans
          (power_succ base finite (m + 1)).symm
      have below : j.val < m + 1 := by
        have := j.isLt
        have : j.val ≠ m + 1 := fun equal => atLast (Fin.ext equal)
        omega
      let earlier : Fin (m + 1) := ⟨j.val, below⟩
      have castSucc : j = earlier.castSucc := Fin.ext rfl
      have previous := power_insertAt base finite m earlier
      have regroup : MeasurableMap (Space.product (Space.product (historySpace Y m) Y) Y)
          (Space.product (Space.product (historySpace Y m) Y) Y)
          (fun value => ((value.1.1, value.2), value.1.2)) :=
        Space.pair_measurable
          (Space.pair_measurable
            (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
            (Space.second_measurable _ _))
          (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))
      have shape := prod_swap_last (power base finite m) base finite regroup
      have insertMeasurable : MeasurableMap
          (Space.product (Space.product (historySpace Y m) Y) Y)
          (Space.product (historySpace Y (m + 1)) Y)
          (fun value => (insertAt earlier value.1.2 value.1.1, value.2)) :=
        Space.product_map (insertAt_measurable Y earlier) (MeasurableMap.identity Y)
      have measurableG : MeasurableMap (Space.product (Space.product (historySpace Y m) Y) Y)
          (historySpace Y (m + 1 + 1))
          (fun value => snoc (insertAt earlier value.1.2 value.1.1) value.2) :=
        fun {set} => MeasurableMap.comp
          (before := fun (value : ((Fin m → α) × α) × α) =>
            (insertAt earlier value.1.2 value.1.1, value.2))
          (snoc_measurable Y (m + 1)) insertMeasurable (set := set)
      have measurableF : MeasurableMap (Space.product (Space.product (historySpace Y m) Y) Y)
          (historySpace Y (m + 1 + 1))
          (fun value => snoc (insertAt earlier value.2 value.1.1) value.1.2) :=
        fun {set} => MeasurableMap.comp
          (before := fun (value : ((Fin m → α) × α) × α) =>
            ((value.1.1, value.2), value.1.2))
          measurableG regroup (set := set)
      have left : (Measure.prod (power base finite (m + 1)) base finite).map
          (fun pair => insertAt j pair.2 pair.1) (insertAt_measurable Y j) =
          (Measure.prod (Measure.prod (power base finite m) base finite) base finite).map
            (fun value => snoc (insertAt earlier value.2 value.1.1) value.1.2) measurableF := by
        rw [power_succ, Measure.prod_map_left, Measure.map_comp]
        refine map_congr_function _ (funext fun value => ?_) _ _
        show insertAt j value.2 (snoc value.1.1 value.1.2) =
          snoc (insertAt earlier value.2 value.1.1) value.1.2
        rw [castSucc, insertAt_snoc]
      have right : power base finite (m + 1 + 1) =
          (Measure.prod (Measure.prod (power base finite m) base finite) base finite).map
            (fun value => snoc (insertAt earlier value.1.2 value.1.1) value.2) measurableG := by
        rw [power_succ, ← previous, Measure.prod_map_left, Measure.map_comp]
      rw [left, right]
      conv => rhs; rw [← shape]
      rw [Measure.map_comp]

/-- Every permutation leaves each power of the base unchanged. -/
theorem power_permute {Y : Space α} (base : Measure Y) (finite : Measure.SFinite base) :
    ∀ (n : Nat) (σ : Perm n),
      (power base finite n).map (permute σ) (permute_measurable Y σ) = power base finite n
  | 0, σ => by
      have identity : permute σ = fun ys : Fin 0 → α => ys :=
        funext fun ys => funext fun index => index.elim0
      rw [map_congr_function _ identity _ (MeasurableMap.identity _), Measure.map_id]
  | n + 1, σ => by
      let j := σ.forward (Fin.last n)
      let ρ := σ.removeAt j
      have previous := power_permute base finite n ρ
      have pushed : MeasurableMap (Space.product (historySpace Y n) Y)
          (Space.product (historySpace Y n) Y) (fun pair => (permute ρ pair.1, pair.2)) :=
        Space.product_map (permute_measurable Y ρ) (MeasurableMap.identity Y)
      have moved : MeasurableMap (Space.product (historySpace Y n) Y) (historySpace Y (n + 1))
          (fun pair => insertAt j pair.2 (permute ρ pair.1)) :=
        fun {set} => MeasurableMap.comp
          (before := fun (pair : (Fin n → α) × α) => (permute ρ pair.1, pair.2))
          (insertAt_measurable Y j) pushed (set := set)
      have split : (Measure.prod (power base finite n) base finite).map
          (fun pair => insertAt j pair.2 (permute ρ pair.1)) moved =
          ((Measure.prod (power base finite n) base finite).map
            (fun pair => (permute ρ pair.1, pair.2)) pushed).map
            (fun pair => insertAt j pair.2 pair.1) (insertAt_measurable Y j) := by
        rw [Measure.map_comp]
      conv => lhs; rw [power_succ, Measure.map_comp]
      rw [map_congr_function _
        (funext fun (pair : (Fin n → α) × α) => permute_snoc σ pair.1 pair.2)
        _ moved, split,
        ← Measure.prod_map_left (power base finite n) base finite (permute ρ)
          (permute_measurable Y ρ), previous, power_insertAt]

end

end Problib.Measure.Exchangeable
