module

public import Problib.Measure.Memo.Cylinder

set_option autoImplicit false

namespace Problib.Measure.Memo
public section
open Problib.Real

namespace Cache

@[expose] def lookup : Cache → Nat → Option Bool
  | [], _ => none
  | value :: _, 0 => value
  | _ :: rest, n + 1 => lookup rest n

/-- Extend the finite cache only as far as the requested coordinate. -/
@[expose] def insert : Cache → Nat → Bool → Cache
  | [], 0, value => [some value]
  | [], n + 1, value => none :: insert [] n value
  | _ :: rest, 0, value => some value :: rest
  | head :: rest, n + 1, value => head :: insert rest n value

theorem lookup_insert (cache : Cache) (written : Nat) (value : Bool) (queried : Nat) :
    lookup (insert cache written value) queried =
      if queried = written then some value else lookup cache queried := by
  induction written generalizing cache queried with
  | zero => cases cache <;> cases queried <;> simp [insert, lookup]
  | succ written induction =>
      cases cache <;> cases queried <;> simp [insert, lookup, induction]

theorem hit {cache : Cache} {key : Nat} {value : Bool}
    (found : lookup cache key = some value) {table : Table} (agrees : Cylinder cache table) :
    table key = value := by
  induction key generalizing cache table with
  | zero =>
      cases cache with
      | nil => cases found
      | cons head rest =>
          cases head with
          | none => cases found
          | some other => cases Option.some.inj found; exact agrees.1
  | succ key induction =>
      cases cache with
      | nil => cases found
      | cons head rest =>
          cases head with
          | none => exact induction found agrees
          | some _ => exact induction found agrees.2

theorem cylinder_insert {cache : Cache} {key : Nat} (value : Bool)
    (fresh : lookup cache key = none) :
    Cylinder (insert cache key value) =
      Set.inter (Cylinder cache) (fun table => table key = value) := by
  induction key generalizing cache with
  | zero =>
      cases cache with
      | nil => apply Set.ext; intro table; exact ⟨fun h => ⟨trivial, h.1⟩, fun h => ⟨h.2, trivial⟩⟩
      | cons head rest =>
          cases head with
          | none => apply Set.ext; intro table; exact and_comm
          | some _ => cases fresh
  | succ key induction =>
      cases cache with
      | nil =>
          apply Set.ext
          intro table
          change Cylinder (insert [] key value) (fun n => table (n + 1)) ↔ _
          rw [induction rfl]
          rfl
      | cons head rest =>
          cases head with
          | none => exact congrArg (fun event => fun table : Table => event (fun n => table (n + 1))) (induction fresh)
          | some head =>
              apply Set.ext
              intro table
              change (table 0 = head ∧ Cylinder (insert rest key value) _) ↔ _
              rw [induction fresh]
              exact and_assoc.symm

theorem weight_insert (bias : Bias) {cache : Cache} {key : Nat} (value : Bool)
    (fresh : lookup cache key = none) :
    cacheWeight bias (insert cache key value) =
      ENNReal.mul (cacheWeight bias cache) (ENNReal.ofReal (Cell.weight (bias key) value)) := by
  induction key generalizing cache bias with
  | zero =>
      cases cache with
      | nil => simp only [insert, cacheWeight, ENNReal.mul_one, ENNReal.one_mul]
      | cons head rest =>
          cases head with
          | none => exact ENNReal.mul_comm _ _
          | some _ => cases fresh
  | succ key induction =>
      cases cache with
      | nil =>
          change cacheWeight (fun n => bias (n + 1)) (insert [] key value) = _
          exact induction _ rfl
      | cons head rest =>
          cases head with
          | none => exact induction _ fresh
          | some head =>
              change ENNReal.mul _ (cacheWeight (fun n => bias (n + 1)) (insert rest key value)) = _
              rw [induction _ fresh]
              exact (ENNReal.mul_assoc _ _ _).symm

end Cache
end
end Problib.Measure.Memo
