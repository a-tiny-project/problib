module

public import Problib.Measure.Memo.Indexed

set_option autoImplicit false

namespace Problib.Measure.Memo
public section
open Problib.Real Problib.Measure.Real

universe u v
variable {κ : Type u} {α : Type v}

namespace Sparse

/-- A finite cache contains only keys actually queried. -/
@[expose] noncomputable def lookup (cache : List (κ × Bool)) (key : κ) : Option Bool :=
  match cache with
  | [] => none
  | (other, value) :: rest => @ite (Option Bool) (key = other) (Classical.propDecidable _)
      (some value) (lookup rest key)

@[expose] noncomputable def run (bias : κ → UnitInterval) (cache : List (κ × Bool)) :
    Query α κ → Set α → ENNReal
  | .ret value, event => @ite ENNReal (event value) (Classical.propDecidable _) ENNReal.one ENNReal.zero
  | .ask key no yes, event =>
      match lookup cache key with
      | some false => run bias cache no event
      | some true => run bias cache yes event
      | none => ENNReal.add
          (ENNReal.mul (ENNReal.ofReal (Cell.weight (bias key) false))
            (run bias ((key, false) :: cache) no event))
          (ENNReal.mul (ENNReal.ofReal (Cell.weight (bias key) true))
            (run bias ((key, true) :: cache) yes event))

/-- Cache simulation tracks equality of facts, independent of the numerical coding. -/
theorem encode_run (encode : κ → Nat) (injective : Function.Injective encode)
    (bias : κ → UnitInterval) (codedBias : Bias) (sameBias : ∀ key, codedBias (encode key) = bias key)
    (query : Query α κ) (cache : List (κ × Bool)) (codedCache : Cache)
    (related : ∀ key, lookup cache key = codedCache.lookup (encode key)) (event : Set α) :
    run bias cache query event = (query.rekey encode).lazy codedBias codedCache event := by
  classical
  induction query generalizing cache codedCache with
  | ret _ => rfl
  | ask key no yes noIH yesIH =>
      have update (value : Bool) : ∀ other,
          lookup ((key, value) :: cache) other =
            (codedCache.insert (encode key) value).lookup (encode other) := by
        intro other
        rw [lookup, Cache.lookup_insert]
        have equal : (encode other = encode key) ↔ other = key := ⟨fun same => injective same, congrArg encode⟩
        simp only [equal, related other]
      cases found : lookup cache key with
      | none =>
          simp only [run, Query.rekey, Query.lazy, ← related key, found, sameBias]
          rw [noIH _ _ (update false), yesIH _ _ (update true)]
      | some value =>
          cases value <;> simp only [run, Query.rekey, Query.lazy, ← related key, found]
          · exact noIH cache codedCache related
          · exact yesIH cache codedCache related

end Sparse

namespace Indexed

/-- Finite adaptive queries on original keys agree with a sparse lazy cache. -/
theorem lazy_eq_table (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key) (bias : κ → UnitInterval)
    (query : Query α κ) (event : Set α) :
    law encode decode bias (Set.preimage query.eval event) = Sparse.run bias [] query event := by
  have mapped := Measure.map_apply (Memo.law (extendBias decode bias))
    (fun table : Table => fun key : κ => table (encode key))
    (show MeasurableMap tableSpace (space κ) _ from
      Space.pi_reindex (fun _ : Nat => Space.discrete Bool) encode)
    (query.eval_measurable (Space.discrete_measurable event))
  have equal : Set.preimage (fun table : Table => fun key : κ => table (encode key))
      (Set.preimage query.eval event) = Set.preimage (query.rekey encode).eval event := by
    apply Set.ext
    intro table
    simp only [Set.preimage, Query.eval_rekey]
  rw [equal, Query.lazy_eq_table] at mapped
  exact mapped.trans (Sparse.encode_run encode (encode_injective encode decode roundTrip)
    bias (extendBias decode bias) (extendBias_encode encode decode roundTrip bias) query [] []
    (fun _ => rfl) event).symm

/-- Distinct keys are independent conditional on their fixed coordinate biases. -/
theorem pair_true (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key) (bias : κ → UnitInterval)
    (first second : κ) (different : second ≠ first) :
    law encode decode bias (fun table => table first = true ∧ table second = true) =
      ENNReal.mul (ENNReal.ofReal (bias first).val) (ENNReal.ofReal (bias second).val) := by
  classical
  let query : Query Bool κ := .ask first (.ret false) (.ask second (.ret false) (.ret true))
  have equal : (fun table : κ → Bool => table first = true ∧ table second = true) =
      Set.preimage query.eval (Set.singleton true) := by
    apply Set.ext
    intro table
    simp only [query, Query.eval, Set.preimage, Set.singleton]
    cases table first <;> cases table second <;> simp
  rw [equal, lazy_eq_table encode decode roundTrip]
  simp only [query, Sparse.run, Sparse.lookup, different, ↓reduceIte, Set.singleton,
    Bool.false_eq_true, ENNReal.mul_zero, ENNReal.mul_one, ENNReal.zero_add, Cell.weight]

/-- Changing a verified encoding cannot change any finite adaptive observation. -/
theorem encoding_independent (first second : κ → Nat) (decodeFirst decodeSecond : Nat → Option κ)
    (firstRoundTrip : ∀ key, decodeFirst (first key) = some key)
    (secondRoundTrip : ∀ key, decodeSecond (second key) = some key)
    (bias : κ → UnitInterval) (query : Query α κ) (event : Set α) :
    law first decodeFirst bias (Set.preimage query.eval event) =
      law second decodeSecond bias (Set.preimage query.eval event) := by
  rw [lazy_eq_table first decodeFirst firstRoundTrip, lazy_eq_table second decodeSecond secondRoundTrip]

end Indexed
end
end Problib.Measure.Memo
