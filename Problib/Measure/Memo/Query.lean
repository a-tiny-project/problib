module

public import Problib.Measure.Memo.Cache

set_option autoImplicit false

namespace Problib.Measure.Memo
public section
open Problib.Real Problib.Measure.Real

universe u v w

/-- Finite adaptive queries may revisit any key in any order. -/
inductive Query (α : Type u) (κ : Type v) where
  | ret (value : α)
  | ask (key : κ) (ifFalse ifTrue : Query α κ)

namespace Query
variable {α : Type u}

@[expose] def eval {κ : Type v} : Query α κ → (κ → Bool) → α
  | .ret value, _ => value
  | .ask key ifFalse ifTrue, table =>
      if table key then ifTrue.eval table else ifFalse.eval table

theorem eval_measurable {κ : Type v} (query : Query α κ) :
    MeasurableMap (Space.pi (fun _ : κ => Space.discrete Bool)) (Space.discrete α) query.eval := by
  induction query with
  | ret value => exact MeasurableMap.constant _ _ value
  | ask key no yes noMeasurable yesMeasurable =>
      intro event _
      have equal : Set.preimage (Query.ask key no yes).eval event =
          Set.union
            (Set.inter (fun table : κ → Bool => table key = false) (Set.preimage no.eval event))
            (Set.inter (fun table : κ → Bool => table key = true) (Set.preimage yes.eval event)) := by
        apply Set.ext
        intro table
        simp only [Set.preimage, Set.union, Set.inter, eval]
        cases table key <;> simp
      rw [equal]
      exact (Space.pi (fun _ : κ => Space.discrete Bool)).union
        ((Space.pi (fun _ : κ => Space.discrete Bool)).inter
          (Space.coordinate_measurable (fun _ : κ => Space.discrete Bool) key
            (Space.discrete_measurable (Set.singleton false))) (noMeasurable trivial))
        ((Space.pi (fun _ : κ => Space.discrete Bool)).inter
          (Space.coordinate_measurable (fun _ : κ => Space.discrete Bool) key
            (Space.discrete_measurable (Set.singleton true))) (yesMeasurable trivial))

/-- Reindex only the requests, preserving the complete adaptive branch tree. -/
@[expose] def rekey {κ : Type v} {ι : Type w} (encode : κ → ι) : Query α κ → Query α ι
  | .ret value => .ret value
  | .ask key no yes => .ask (encode key) (rekey encode no) (rekey encode yes)

theorem eval_rekey {κ : Type v} {ι : Type w} (encode : κ → ι) (query : Query α κ)
    (table : ι → Bool) : (query.rekey encode).eval table = query.eval (fun key => table (encode key)) := by
  induction query with
  | ret _ => rfl
  | ask key no yes noIH yesIH => simp only [rekey, eval, noIH, yesIH]

/-- Exact lazy execution: hits reuse a fact; misses draw and remember one fact. -/
@[expose] noncomputable def lazy (bias : Bias) (cache : Cache) : Query α Nat → Set α → ENNReal
  | .ret value, event => @ite ENNReal (event value) (Classical.propDecidable _) ENNReal.one ENNReal.zero
  | .ask key no yes, event =>
      match cache.lookup key with
      | some false => lazy bias cache no event
      | some true => lazy bias cache yes event
      | none => ENNReal.add
          (ENNReal.mul (ENNReal.ofReal (Cell.weight (bias key) false))
            (lazy bias (cache.insert key false) no event))
          (ENNReal.mul (ENNReal.ofReal (Cell.weight (bias key) true))
            (lazy bias (cache.insert key true) yes event))

@[expose] def region (cache : Cache) (query : Query α Nat) (event : Set α) : Set Table :=
  Set.inter (Cylinder cache) (Set.preimage query.eval event)

theorem region_measurable (cache : Cache) (query : Query α Nat) (event : Set α) :
    tableSpace.Measurable (region cache query event) :=
  tableSpace.inter (cylinder_measurable cache)
    (query.eval_measurable (Space.discrete_measurable event))

private theorem region_miss {cache : Cache} {key : Nat} (fresh : cache.lookup key = none)
    (no yes : Query α Nat) (event : Set α) :
    region cache (.ask key no yes) event =
      Set.union (region (cache.insert key false) no event)
        (region (cache.insert key true) yes event) := by
  apply Set.ext
  intro table
  simp only [region, Cache.cylinder_insert _ fresh, Set.inter, Set.union, Set.preimage, eval]
  cases table key <;> simp

private theorem region_miss_disjoint {cache : Cache} {key : Nat} (fresh : cache.lookup key = none)
    (no yes : Query α Nat) (event : Set α) :
    Set.Disjoint (region (cache.insert key false) no event)
      (region (cache.insert key true) yes event) := by
  intro table left right
  have leftValue := (congrFun (Cache.cylinder_insert false fresh) table).mp left.1
  have rightValue := (congrFun (Cache.cylinder_insert true fresh) table).mp right.1
  exact Bool.noConfusion (leftValue.2.symm.trans rightValue.2)

/-- Unnormalized correctness also covers impossible caches, without division. -/
theorem law_region (bias : Bias) (query : Query α Nat) (cache : Cache) (event : Set α) :
    law bias (region cache query event) =
      ENNReal.mul (cacheWeight bias cache) (lazy bias cache query event) := by
  classical
  induction query generalizing cache with
  | ret value =>
      by_cases member : event value
      · have equal : region cache (.ret value) event = Cylinder cache := by
          apply Set.ext; intro table; exact ⟨And.left, fun h => ⟨h, member⟩⟩
        rw [equal, law_cylinder]
        simp only [lazy, if_pos member, ENNReal.mul_one]
      · have equal : region cache (.ret value) event = Set.empty := by
          apply Set.ext; intro table; exact ⟨fun h => member h.2, False.elim⟩
        rw [equal, Measure.empty_apply]
        simp only [lazy, if_neg member, ENNReal.mul_zero]
  | ask key no yes noInduction yesInduction =>
      cases found : cache.lookup key with
      | none =>
          rw [region_miss found, Measure.union_disjoint _
            (region_measurable _ _ _) (region_measurable _ _ _) (region_miss_disjoint found _ _ _),
            noInduction, yesInduction, Cache.weight_insert _ _ found, Cache.weight_insert _ _ found]
          simp only [lazy, found]
          rw [ENNReal.mul_assoc, ENNReal.mul_assoc, ← ENNReal.mul_add]
      | some value =>
          have selected : ∀ table, Cylinder cache table → table key = value := fun _ => Cache.hit found
          cases value with
          | false =>
              have equal : region cache (.ask key no yes) event = region cache no event := by
                apply Set.ext
                intro table
                constructor
                · intro member
                  exact ⟨member.1, by simpa [Set.preimage, eval, selected table member.1] using member.2⟩
                · intro member
                  exact ⟨member.1, by simpa [Set.preimage, eval, selected table member.1] using member.2⟩
              rw [equal, noInduction]
              simp only [lazy, found]
          | true =>
              have equal : region cache (.ask key no yes) event = region cache yes event := by
                apply Set.ext
                intro table
                constructor
                · intro member
                  exact ⟨member.1, by simpa [Set.preimage, eval, selected table member.1] using member.2⟩
                · intro member
                  exact ⟨member.1, by simpa [Set.preimage, eval, selected table member.1] using member.2⟩
              rw [equal, yesInduction]
              simp only [lazy, found]

/-- Sampling a whole world and lazily sampling its queried facts have the same law. -/
theorem lazy_eq_table (bias : Bias) (query : Query α Nat) (event : Set α) :
    law bias (Set.preimage query.eval event) = lazy bias [] query event := by
  have correct := law_region bias query [] event
  have equal : region [] query event = Set.preimage query.eval event := by
    apply Set.ext; intro table; exact ⟨And.right, fun h => ⟨trivial, h⟩⟩
  rw [equal, cacheWeight, ENNReal.one_mul] at correct
  exact correct

/-- Query rearrangements preserve answers whenever they read the same world function. -/
theorem lazy_congr (bias : Bias) (left right : Query α Nat)
    (equal : ∀ table, left.eval table = right.eval table) (event : Set α) :
    lazy bias [] left event = lazy bias [] right event := by
  rw [← lazy_eq_table, ← lazy_eq_table]
  exact congrArg (fun evaluate => law bias (Set.preimage evaluate event)) (funext equal)

end Query
end
end Problib.Measure.Memo
