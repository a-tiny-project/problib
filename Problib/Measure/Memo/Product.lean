module

public import Problib.Measure.Memo.Sparse
public import Problib.Measure.Kernel.Pi.Law

set_option autoImplicit false

/-!
# Memo tables are product laws

A memo table reads distinct keys independently: a joint reading of distinct
keys has the product of the per-key weights. A finite check that asks each key
once computes that mass through the sparse lazy run. The table law is
therefore the product of its coordinate laws, because points determine
measures on `Bool`.
-/

namespace Problib.Measure.Memo
public section
open Problib.Real Problib.Measure.Real

universe u

variable {κ : Type u}

namespace Sparse

/-- Ask each listed key once, and answer `true` when every reading matches
`entries`. -/
@[expose] def check (entries : κ → Bool) : List κ → Query Bool κ
  | [] => .ret true
  | key :: rest => match entries key with
      | false => .ask key (check entries rest) (.ret false)
      | true => .ask key (.ret false) (check entries rest)

theorem eval_check (entries : κ → Bool) (table : κ → Bool) :
    (keys : List κ) →
      ((check entries keys).eval table = true ↔ ∀ key ∈ keys, table key = entries key)
  | [] => ⟨fun _ _ member => (nomatch member), fun _ => rfl⟩
  | key :: rest => by
      have tail := eval_check entries table rest
      simp only [List.mem_cons, forall_eq_or_imp]
      cases found : entries key <;> cases reading : table key <;>
        simp [check, Query.eval, found, reading, tail]

/-- The sparse run of the check, from a cache that holds none of its keys, is
the product of the per-key weights of the checked entries. -/
theorem run_check (bias : κ → UnitInterval) (entries : κ → Bool) :
    (keys : List κ) → keys.Nodup → (cache : List (κ × Bool)) →
    (∀ key ∈ keys, lookup cache key = none) →
    run bias cache (check entries keys) (Set.singleton true) =
      Pi.massProduct keys fun key => ENNReal.ofReal (Cell.weight (bias key) (entries key))
  | [], _, _, _ => by
      simp only [check, run, Set.singleton]
      rfl
  | key :: rest, distinctKeys, cache, fresh => by
      have restFresh (value : Bool) : ∀ other ∈ rest,
          lookup ((key, value) :: cache) other = none := by
        intro other member
        have different : other ≠ key := fun same =>
          (List.nodup_cons.mp distinctKeys).1 (same ▸ member)
        simp only [lookup, different, ↓reduceIte]
        exact fresh other (List.Mem.tail _ member)
      have restRun (value : Bool) := run_check bias entries rest
        (List.nodup_cons.mp distinctKeys).2 ((key, value) :: cache) (restFresh value)
      change _ = ENNReal.mul _ (Pi.massProduct rest _)
      cases found : entries key with
      | false =>
          simp only [check, found, run, fresh key (List.Mem.head _), restRun,
            Set.singleton, Bool.false_eq_true, ↓reduceIte, ENNReal.mul_zero, ENNReal.add_zero]
      | true =>
          simp only [check, found, run, fresh key (List.Mem.head _), restRun,
            Set.singleton, Bool.false_eq_true, ↓reduceIte, ENNReal.mul_zero, ENNReal.zero_add]

end Sparse

namespace Indexed

/-- Distinct keys read given entries with the product of their per-key
weights. -/
theorem law_entries (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key) (bias : κ → UnitInterval)
    (entries : κ → Bool) {keys : List κ} (distinctKeys : keys.Nodup) :
    law encode decode bias (fun table => ∀ key ∈ keys, table key = entries key) =
      Pi.massProduct keys fun key => ENNReal.ofReal (Cell.weight (bias key) (entries key)) := by
  have equal : (fun table : κ → Bool => ∀ key ∈ keys, table key = entries key) =
      Set.preimage (Sparse.check entries keys).eval (Set.singleton true) := by
    apply Set.ext
    intro table
    exact (Sparse.eval_check entries table keys).symm
  rw [equal, lazy_eq_table encode decode roundTrip]
  exact Sparse.run_check bias entries keys distinctKeys [] fun _ _ => rfl

/-- Each key reads a value with that value's weight. -/
theorem law_reading (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key) (bias : κ → UnitInterval)
    (key : κ) (value : Bool) :
    (law encode decode bias).map (fun table => table key)
        (Space.coordinate_measurable (fun _ : κ => Space.discrete Bool) key)
        (Set.singleton value) =
      ENNReal.ofReal (Cell.weight (bias key) value) := by
  refine (Measure.map_apply (law encode decode bias) (fun table : κ → Bool => table key)
    (Space.coordinate_measurable (fun _ : κ => Space.discrete Bool) key)
    (Space.discrete_measurable (Set.singleton value))).trans ?_
  have single := law_entries encode decode roundTrip bias (fun _ => value) (keys := [key])
    (List.nodup_cons.mpr ⟨fun member => (nomatch member), List.nodup_nil⟩)
  have equal : Set.preimage (fun table : κ → Bool => table key) (Set.singleton value) =
      fun table => ∀ other ∈ [key], table other = value := by
    apply Set.ext
    intro table
    constructor
    · intro same other member
      rw [List.mem_singleton.mp member]
      exact same
    · intro inside
      exact inside key (List.Mem.head _)
  rw [equal, single, Pi.massProduct_cons, Pi.massProduct_nil, ENNReal.mul_one]

/-- A memo table law is the product of its coordinate laws: distinct keys are
independent. -/
theorem law_isProduct (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key) (bias : κ → UnitInterval) :
    Pi.IsProduct (law encode decode bias) fun key =>
      (law encode decode bias).map (fun table => table key)
        (Space.coordinate_measurable (fun _ : κ => Space.discrete Bool) key) := by
  have injective : Function.Injective fun value : Bool => if value then 1 else 0 := by
    intro left right same
    cases left <;> cases right <;> simp_all
  apply Pi.IsProduct.of_determining (Pi.Determining.singletons _ injective)
    fun key => ((law_probability encode decode bias).map _ _).to_finite
  intro keys distinctKeys sets singletons
  have choice : ∀ key, ∃ value : Bool, key ∈ keys → sets key = Set.singleton value := by
    intro key
    by_cases member : key ∈ keys
    · obtain ⟨value, equal⟩ := singletons key member
      exact ⟨value, fun _ => equal⟩
    · exact ⟨false, fun inside => absurd inside member⟩
  obtain ⟨entries, entriesSpec⟩ := Classical.axiomOfChoice choice
  rw [Pi.cylinder_congr entriesSpec]
  change law encode decode bias (fun table => ∀ key ∈ keys, table key = entries key) = _
  rw [law_entries encode decode roundTrip bias entries distinctKeys]
  exact Pi.massProduct_congr fun key member => by
    rw [entriesSpec key member, law_reading encode decode roundTrip]

end Indexed

/-- The table law over the naturals is the indexed law at the identity code. -/
theorem law_natural (bias : Bias) : Indexed.law (fun n : Nat => n) some bias = law bias := by
  have biasEq : Indexed.extendBias some bias = bias := rfl
  unfold Indexed.law
  rw [biasEq]
  exact Measure.map_id (law bias)

/-- The table law over the naturals is the product of its coordinate laws. -/
theorem law_isProduct (bias : Bias) :
    Pi.IsProduct (law bias) fun n =>
      (law bias).map (fun table => table n)
        (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) n) := by
  have product := Indexed.law_isProduct (fun n : Nat => n) some (fun _ => rfl) bias
  rw [law_natural] at product
  exact product

/-- Coordinates with the same bias have the same law. -/
theorem law_marginal_congr (bias : Bias) {first second : Nat} (same : bias first = bias second) :
    (law bias).map (fun table => table first)
        (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) first) =
      (law bias).map (fun table => table second)
        (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) second) := by
  apply Measure.IsProbability.bool_ext
    ((law_probability bias).map _ (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) first))
    ((law_probability bias).map _ (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) second))
  have firstTrue := Measure.map_apply (law bias) (fun table : Table => table first)
    (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) first)
    (Space.discrete_measurable (Set.singleton true))
  have secondTrue := Measure.map_apply (law bias) (fun table : Table => table second)
    (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) second)
    (Space.discrete_measurable (Set.singleton true))
  refine firstTrue.trans (Eq.trans ?_ secondTrue.symm)
  change law bias (fun table => table first = true) = law bias (fun table => table second = true)
  rw [law_coordinate_true, law_coordinate_true, same]

end
end Problib.Measure.Memo
