module

public import Problib.Measure.Memo.Table

set_option autoImplicit false

namespace Problib.Measure.Memo
public section
open Problib.Real Problib.Real.Construction
open Problib.Measure.Real Dedekind

abbrev Cache := List (Option Bool)

/-- A finite observation records some coordinates and leaves others unqueried. -/
@[expose] def Cylinder : Cache → Set Table
  | [], _ => True
  | none :: rest, table => Cylinder rest (fun n => table (n + 1))
  | some value :: rest, table => table 0 = value ∧ Cylinder rest (fun n => table (n + 1))

@[expose] noncomputable def cacheWeight (bias : Bias) : Cache → ENNReal
  | [] => ENNReal.one
  | none :: rest => cacheWeight (fun n => bias (n + 1)) rest
  | some value :: rest => ENNReal.mul (ENNReal.ofReal (Cell.weight (bias 0) value))
      (cacheWeight (fun n => bias (n + 1)) rest)

theorem cylinder_measurable (cache : Cache) : tableSpace.Measurable (Cylinder cache) := by
  induction cache with
  | nil => exact tableSpace.univ
  | cons value rest induction =>
      have tail := Space.pi_reindex (fun _ : Nat => Space.discrete Bool) Nat.succ induction
      cases value with
      | none => exact tail
      | some value =>
          exact tableSpace.inter
            (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) 0
              (Space.discrete_measurable (Set.singleton value))) tail

theorem cylinder_full (word : List Bool) : Cylinder (word.map some) = Prefix word := by
  induction word with
  | nil => rfl
  | cons value rest induction => simp only [List.map_cons, Cylinder, Prefix, induction]

theorem cacheWeight_full (bias : Bias) (word : List Bool) :
    cacheWeight bias (word.map some) = wordWeight bias word := by
  induction word generalizing bias with
  | nil => rfl
  | cons value rest induction => simp only [List.map_cons, cacheWeight, wordWeight, induction]

theorem weight_sum (bias : UnitInterval) :
    ENNReal.add (ENNReal.ofReal (Cell.weight bias false))
      (ENNReal.ofReal (Cell.weight bias true)) = ENNReal.one := by
  rw [← ENNReal.ofReal_add (Cell.weight_nonnegative bias false) (Cell.weight_nonnegative bias true)]
  have equal : add (Cell.weight bias false) (Cell.weight bias true) = one := by
    change add (sub one bias.val) bias.val = one
    rw [Dedekind.sub_eq_add_neg, Dedekind.add_assoc, Dedekind.add_comm (neg bias.val), Dedekind.add_neg, Dedekind.add_zero]
  rw [equal]
  exact ENNReal.ofReal_toReal_finite NNReal.one

theorem cylinder_split (before : List Bool) (rest : Cache) :
    Cylinder (before.map some ++ none :: rest) =
      Set.union (Cylinder (before.map some ++ some false :: rest))
        (Cylinder (before.map some ++ some true :: rest)) := by
  induction before with
  | nil =>
      apply Set.ext
      intro table
      change Cylinder rest _ ↔ (table 0 = false ∧ Cylinder rest _) ∨
        (table 0 = true ∧ Cylinder rest _)
      cases table 0 <;> simp
  | cons value before induction =>
      apply Set.ext
      intro table
      change (table 0 = value ∧ Cylinder (before.map some ++ none :: rest) _) ↔ _
      rw [induction]
      exact and_or_left

theorem cylinder_split_disjoint (before : List Bool) (rest : Cache) :
    Set.Disjoint (Cylinder (before.map some ++ some false :: rest))
      (Cylinder (before.map some ++ some true :: rest)) := by
  induction before with
  | nil => intro table left right; exact Bool.noConfusion (left.1.symm.trans right.1)
  | cons value before induction => intro table left right; exact induction left.2 right.2

theorem cacheWeight_split (bias : Bias) (before : List Bool) (rest : Cache) :
    ENNReal.add (cacheWeight bias (before.map some ++ some false :: rest))
      (cacheWeight bias (before.map some ++ some true :: rest)) =
      cacheWeight bias (before.map some ++ none :: rest) := by
  induction before generalizing bias with
  | nil =>
      change ENNReal.add (ENNReal.mul _ _) (ENNReal.mul _ _) = _
      rw [ENNReal.mul_comm (ENNReal.ofReal (Cell.weight (bias 0) false)),
        ENNReal.mul_comm (ENNReal.ofReal (Cell.weight (bias 0) true)),
        ← ENNReal.mul_add, weight_sum, ENNReal.mul_one]
      rfl
  | cons value before induction =>
      simp only [List.map_cons, List.cons_append, cacheWeight]
      rw [← ENNReal.mul_add, induction]

/-- Arbitrary finite coordinate observations, including gaps, have product mass. -/
theorem law_cylinder (bias : Bias) (cache : Cache) :
    law bias (Cylinder cache) = cacheWeight bias cache := by
  have generalized : ∀ (rest : Cache) (before : List Bool),
      law bias (Cylinder (before.map some ++ rest)) =
        cacheWeight bias (before.map some ++ rest) := by
    intro rest
    induction rest with
    | nil => intro before; simpa only [List.append_nil, cylinder_full, cacheWeight_full] using law_prefix bias before
    | cons value rest induction =>
        intro before
        have append (value : Bool) : before.map some ++ some value :: rest =
            (before ++ [value]).map some ++ rest := by simp
        cases value with
        | some value => rw [append]; exact induction _
        | none =>
            rw [cylinder_split, Measure.union_disjoint _
              (cylinder_measurable _) (cylinder_measurable _) (cylinder_split_disjoint _ _)]
            rw [append false, append true, induction, induction, ← append false, ← append true]
            exact cacheWeight_split bias before rest
  exact generalized cache []

end
end Problib.Measure.Memo
