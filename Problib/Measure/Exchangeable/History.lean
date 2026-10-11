module

public import Problib.Measure.Exchangeable.Perm
public import Problib.Measure.Pi
public import Problib.Measure.Configuration.Shape
public import Problib.Measure.Kernel.Product.Algebra

set_option autoImplicit false

/-!
# Finite histories

A history of `n` observations is a map `Fin n → α` on the product space. A
permutation acts on it by moving the observation in slot `σ⁻¹ i` to slot `i`
(`permute`), `eraseAt i` forgets slot `i`, and `snoc` appends one observation
at the end. `power base n` is the `n`-fold product of an s-finite base measure,
built one appended coordinate at a time.
-/

namespace Problib.Measure.Exchangeable

open Problib.Real

public section

universe u

variable {α : Type u} {n : Nat}

/-- The measurable space of histories of `n` observations. -/
@[expose] def historySpace (Y : Space α) (n : Nat) : Space (Fin n → α) :=
  Space.pi fun _ => Y

/-- The history whose slot `i` holds the observation in slot `σ⁻¹ i`. -/
@[expose] def permute (σ : Perm n) (ys : Fin n → α) : Fin n → α :=
  fun index => ys (σ.inverse index)

/-- The history without slot `i`, in order. -/
@[expose] def eraseAt (i : Fin (n + 1)) (ys : Fin (n + 1) → α) : Fin n → α :=
  fun index => ys (skip i index)

/-- The history with `y` appended after its last slot. -/
@[expose] def snoc (ys : Fin n → α) (y : α) : Fin (n + 1) → α :=
  fun index => if below : index.val < n then ys ⟨index.val, below⟩ else y

/-- The history as a list, first slot first. -/
@[expose] def toList (ys : Fin n → α) : List α :=
  List.ofFn ys

/-- The empty history. -/
@[expose] def empty : Fin 0 → α :=
  fun index => index.elim0

theorem snoc_castSucc (ys : Fin n → α) (y : α) (index : Fin n) :
    snoc ys y index.castSucc = ys index := by
  simp [snoc, index.isLt]

theorem snoc_last (ys : Fin n → α) (y : α) : snoc ys y (Fin.last n) = y := by
  simp [snoc]

/-- Listing a history without slot `i` lists it and erases position `i`. -/
theorem toList_eraseAt (i : Fin (n + 1)) (ys : Fin (n + 1) → α) :
    toList (eraseAt i ys) = (toList ys).eraseIdx i.val := by
  unfold toList
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_eraseIdx_of_lt (by rw [List.length_ofFn]; exact i.isLt),
      List.length_ofFn]
    rfl
  · intro k inside _
    rw [List.getElem_ofFn, List.getElem_eraseIdx]
    rw [List.length_ofFn] at inside
    show ys (skip i ⟨k, inside⟩) = _
    split
    · rename_i below
      rw [List.getElem_ofFn]
      exact congrArg ys (Fin.ext (by rw [skip_val]; simp [below]))
    · rename_i above
      rw [List.getElem_ofFn]
      exact congrArg ys (Fin.ext (by rw [skip_val]; simp [above]))

theorem toList_snoc (ys : Fin n → α) (y : α) : toList (snoc ys y) = toList ys ++ [y] := by
  unfold toList
  rw [List.ofFn_succ_last]
  simp only [snoc_castSucc, snoc_last]

theorem toList_empty (ys : Fin 0 → α) : toList ys = [] :=
  List.ofFn_zero

theorem permute_measurable (Y : Space α) (σ : Perm n) :
    MeasurableMap (historySpace Y n) (historySpace Y n) (permute σ) :=
  Space.pi_reindex (fun _ => Y) σ.inverse

theorem eraseAt_measurable (Y : Space α) (i : Fin (n + 1)) :
    MeasurableMap (historySpace Y (n + 1)) (historySpace Y n) (eraseAt i) :=
  Space.pi_reindex (fun _ => Y) (skip i)

theorem snoc_measurable (Y : Space α) (n : Nat) :
    MeasurableMap (Space.product (historySpace Y n) Y) (historySpace Y (n + 1))
      (fun pair => snoc pair.1 pair.2) := by
  apply Space.pi_measurable
  intro index
  by_cases below : index.val < n
  · have equal : (fun pair : (Fin n → α) × α => snoc pair.1 pair.2 index) =
        (fun pair => pair.1 ⟨index.val, below⟩) := by
      funext pair
      simp [snoc, below]
    rw [equal]
    exact MeasurableMap.comp (Space.coordinate_measurable (fun _ => Y) _)
      (Space.first_measurable _ _)
  · have equal : (fun pair : (Fin n → α) × α => snoc pair.1 pair.2 index) =
        (fun pair => pair.2) := by
      funext pair
      simp [snoc, below]
    rw [equal]
    exact Space.second_measurable _ _

theorem snoc_init_last (ys : Fin (n + 1) → α) :
    snoc (fun index => ys index.castSucc) (ys (Fin.last n)) = ys := by
  funext index
  by_cases below : index.val < n
  · simp only [snoc, below, dite_true]
    exact congrArg ys (Fin.ext rfl)
  · simp only [snoc, below, dite_false]
    exact congrArg ys (Fin.ext (by have := index.isLt; simp; omega))

/-- Every set of histories of natural numbers is measurable: the history space
is the discrete space. -/
theorem historySpace_nat_measurable : ∀ (n : Nat) (set : Set (Fin n → Nat)),
    (historySpace (Space.discrete Nat) n).Measurable set
  | 0, set => by
      have point : ∀ ys : Fin 0 → Nat, ys = empty := fun ys => funext fun index => index.elim0
      by_cases holds : set empty
      · have equal : set = Set.univ :=
          Set.ext fun ys => ⟨fun _ => True.intro, fun _ => point ys ▸ holds⟩
        rw [equal]
        exact Space.univ _
      · have equal : set = Set.empty :=
          Set.ext fun ys => ⟨fun member => holds (point ys ▸ member), False.elim⟩
        rw [equal]
        exact Space.empty _
  | n + 1, set => by
      let split : (Fin (n + 1) → Nat) → (Fin n → Nat) × Nat :=
        fun ys => (fun index => ys index.castSucc, ys (Fin.last n))
      have splitMeasurable : MeasurableMap (historySpace (Space.discrete Nat) (n + 1))
          (Space.product (historySpace (Space.discrete Nat) n) (Space.discrete Nat)) split :=
        Space.pair_measurable (Space.pi_reindex (fun _ => Space.discrete Nat) Fin.castSucc)
          (Space.coordinate_measurable (fun _ => Space.discrete Nat) (Fin.last n))
      let pieces : Nat → Set ((Fin n → Nat) × Nat) := fun last =>
        Set.product (fun ys => set (snoc ys last)) (fun value => value = last)
      have union :
          (Space.product (historySpace (Space.discrete Nat) n) (Space.discrete Nat)).Measurable
            (Set.iUnion pieces) :=
        Space.iUnion _ fun last => Space.product_set_measurable _ _
          (historySpace_nat_measurable n _) (Space.discrete_measurable _)
      have equal : set = Set.preimage split (Set.iUnion pieces) := by
        apply Set.ext
        intro ys
        constructor
        · intro member
          refine ⟨ys (Fin.last n), ?_, rfl⟩
          change set (snoc (fun index => ys index.castSucc) (ys (Fin.last n)))
          rw [snoc_init_last]
          exact member
        · rintro ⟨last, member, same⟩
          change set (snoc (fun index => ys index.castSucc) last) at member
          change ys (Fin.last n) = last at same
          rw [← same, snoc_init_last] at member
          exact member
      rw [equal]
      exact splitMeasurable union

theorem toList_measurable (Y : Space α) (n : Nat) :
    MeasurableMap (historySpace Y n) (Space.list Y) toList :=
  ofFn_measurable Y n

/-- The `n`-fold product of `base` with its s-finiteness certificate. -/
@[expose] noncomputable def powerWithFinite {Y : Space α} (base : Measure Y)
    (finite : Measure.SFinite base) :
    (n : Nat) → Σ law : Measure (historySpace Y n), Measure.SFinite law
  | 0 => ⟨Measure.dirac _ empty, Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ _)⟩
  | n + 1 =>
      let previous := powerWithFinite base finite n
      ⟨(Measure.prod previous.1 base finite).map (fun pair => snoc pair.1 pair.2)
          (snoc_measurable Y n),
        (Measure.SFinite.prod previous.2 finite).map (fun pair => snoc pair.1 pair.2)
          (snoc_measurable Y n)⟩

/-- The `n`-fold product of `base`: the Dirac law at the empty history, then
one more independent coordinate from `base` appended at each step. -/
@[expose] noncomputable def power {Y : Space α} (base : Measure Y)
    (finite : Measure.SFinite base) (n : Nat) : Measure (historySpace Y n) :=
  (powerWithFinite base finite n).1

/-- Each power of an s-finite base is s-finite. -/
noncomputable def power_sfinite {Y : Space α} (base : Measure Y)
    (finite : Measure.SFinite base) (n : Nat) : Measure.SFinite (power base finite n) :=
  (powerWithFinite base finite n).2

theorem power_zero {Y : Space α} (base : Measure Y) (finite : Measure.SFinite base) :
    power base finite 0 = Measure.dirac _ empty := rfl

theorem power_succ {Y : Space α} (base : Measure Y) (finite : Measure.SFinite base)
    (n : Nat) :
    power base finite (n + 1) =
      (Measure.prod (power base finite n) base finite).map (fun pair => snoc pair.1 pair.2)
        (snoc_measurable Y n) := rfl

end

end Problib.Measure.Exchangeable
