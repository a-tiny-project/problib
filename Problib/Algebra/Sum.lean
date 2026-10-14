module

public import Problib.Algebra

/-! Finite sums over additive commutative monoid laws.

`listSum` adds the members of a list in order, and `finSum` adds a vector
indexed by `Fin dimension`: the leading entry plus the sum of the rest. The
successor split `finSum (n + 1) f = f 0 + finSum n (fun i => f i.succ)` holds by
`rfl`, so a definitional proof over a vector keeps working after it moves onto
this layer. `finSum_eq_listSum` relates the two folds through `List.finRange`.

Every lemma takes the laws explicitly. At a carrier whose law record is
reducible, `simp` and `dsimp` turn the record's `zero` and `add` into the
carrier's own operations.
-/

set_option autoImplicit false

namespace Problib.Algebra

universe u v

namespace AdditiveCommutativeMonoidLaws

variable {α : Type}

/-- The sum of a list. -/
@[expose] public def listSum (laws : AdditiveCommutativeMonoidLaws α) : List α → α
  | [] => laws.zero
  | value :: values => laws.add value (listSum laws values)

public theorem listSum_nil (laws : AdditiveCommutativeMonoidLaws α) :
    laws.listSum [] = laws.zero :=
  rfl

public theorem listSum_cons (laws : AdditiveCommutativeMonoidLaws α)
    (value : α) (values : List α) :
    laws.listSum (value :: values) = laws.add value (laws.listSum values) :=
  rfl

/-- Summing a concatenation adds the two sums. -/
public theorem listSum_append (laws : AdditiveCommutativeMonoidLaws α)
    (left right : List α) :
    laws.listSum (left ++ right) = laws.add (laws.listSum left) (laws.listSum right) := by
  induction left with
  | nil => exact (laws.zero_add _).symm
  | cons value values induction =>
      show laws.add value (laws.listSum (values ++ right)) = _
      rw [induction, ← laws.add_assoc]
      rfl

/-- A sum of listed terms is the right fold that adds each term. -/
public theorem listSum_map_eq_foldr (laws : AdditiveCommutativeMonoidLaws α)
    {ι : Type u} (indices : List ι) (values : ι → α) :
    laws.listSum (indices.map values) =
      indices.foldr (fun index total => laws.add (values index) total) laws.zero := by
  induction indices with
  | nil => rfl
  | cons index indices induction => exact congrArg (laws.add (values index)) induction

/-- Reordering the members leaves the sum unchanged. -/
public theorem listSum_perm (laws : AdditiveCommutativeMonoidLaws α)
    {left right : List α} (permutation : left.Perm right) :
    laws.listSum left = laws.listSum right := by
  induction permutation with
  | nil => rfl
  | cons value _ induction =>
      exact congrArg (laws.add value) induction
  | swap first second values =>
      exact laws.add_left_comm second first (laws.listSum values)
  | trans _ _ first second => exact first.trans second

/-- Terms that agree on every listed index have the same sum. -/
public theorem listSum_map_congr (laws : AdditiveCommutativeMonoidLaws α)
    {ι : Type u} (indices : List ι) {left right : ι → α}
    (equal : ∀ index, index ∈ indices → left index = right index) :
    laws.listSum (indices.map left) = laws.listSum (indices.map right) :=
  congrArg laws.listSum (List.map_congr_left equal)

/-- A sum whose every listed term vanishes vanishes. -/
public theorem listSum_map_eq_zero (laws : AdditiveCommutativeMonoidLaws α)
    {ι : Type u} (indices : List ι) (values : ι → α)
    (vanishing : ∀ index, index ∈ indices → values index = laws.zero) :
    laws.listSum (indices.map values) = laws.zero := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      show laws.add (values index) (laws.listSum (indices.map values)) = laws.zero
      rw [vanishing index List.mem_cons_self,
        induction (fun other member => vanishing other (List.mem_cons_of_mem index member)),
        laws.add_zero]

/-- The sum of the zero function is zero. -/
public theorem listSum_map_zero (laws : AdditiveCommutativeMonoidLaws α)
    {ι : Type u} (indices : List ι) :
    laws.listSum (indices.map fun _ => laws.zero) = laws.zero :=
  laws.listSum_map_eq_zero indices _ (fun _ _ => rfl)

/-- The sum of a pointwise sum is the sum of the two sums. -/
public theorem listSum_map_add (laws : AdditiveCommutativeMonoidLaws α)
    {ι : Type u} (indices : List ι) (left right : ι → α) :
    laws.listSum (indices.map fun index => laws.add (left index) (right index)) =
      laws.add (laws.listSum (indices.map left)) (laws.listSum (indices.map right)) := by
  induction indices with
  | nil => exact (laws.add_zero laws.zero).symm
  | cons index indices induction =>
      show laws.add (laws.add (left index) (right index))
          (laws.listSum (indices.map fun index => laws.add (left index) (right index))) =
        laws.add (laws.add (left index) (laws.listSum (indices.map left)))
          (laws.add (right index) (laws.listSum (indices.map right)))
      rw [induction, laws.add_assoc, laws.add_assoc,
        laws.add_left_comm (right index) (laws.listSum (indices.map left))]

/-- Over a duplicate-free index list, a sum whose terms vanish away from one
listed index is that index's term. -/
public theorem listSum_map_eq_single (laws : AdditiveCommutativeMonoidLaws α)
    {ι : Type u} (indices : List ι) (target : ι) (nodup : indices.Nodup)
    (member : target ∈ indices) (values : ι → α)
    (vanishing : ∀ index, index ∈ indices → index ≠ target → values index = laws.zero) :
    laws.listSum (indices.map values) = values target := by
  induction indices with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons index indices induction =>
      have indexFresh := (List.nodup_cons.mp nodup).1
      show laws.add (values index) (laws.listSum (indices.map values)) = values target
      rcases List.mem_cons.mp member with equal | inTail
      · subst index
        rw [laws.listSum_map_eq_zero indices values (fun other otherMember =>
            vanishing other (List.mem_cons_of_mem target otherMember)
              (fun same => indexFresh (same ▸ otherMember))),
          laws.add_zero]
      · have different : index ≠ target := fun same => indexFresh (same ▸ inTail)
        rw [vanishing index List.mem_cons_self different, laws.zero_add]
        exact induction (List.nodup_cons.mp nodup).2 inTail
          (fun other otherMember => vanishing other (List.mem_cons_of_mem index otherMember))

/-- A double sum may be taken in either order. -/
public theorem listSum_comm (laws : AdditiveCommutativeMonoidLaws α)
    {ι : Type u} {κ : Type v} (left : List ι) (right : List κ) (values : ι → κ → α) :
    laws.listSum (left.map fun first => laws.listSum (right.map (values first))) =
      laws.listSum (right.map fun second =>
        laws.listSum (left.map fun first => values first second)) := by
  induction left with
  | nil => exact (laws.listSum_map_zero right).symm
  | cons first left induction =>
      show laws.add (laws.listSum (right.map (values first)))
          (laws.listSum (left.map fun first => laws.listSum (right.map (values first)))) = _
      rw [induction]
      exact (laws.listSum_map_add right (values first)
        (fun second => laws.listSum (left.map fun first => values first second))).symm

/-- Summing a flattened family of lists sums the sums of its members. -/
public theorem listSum_flatMap (laws : AdditiveCommutativeMonoidLaws α)
    {ι : Type u} {κ : Type v} (indices : List ι) (entries : ι → List κ)
    (values : ι → κ → α) :
    laws.listSum (indices.flatMap fun index => (entries index).map (values index)) =
      laws.listSum (indices.map fun index =>
        laws.listSum ((entries index).map (values index))) := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      rw [List.flatMap_cons, laws.listSum_append, induction]
      rfl

/-- A map that preserves zero and addition carries a sum to the sum of the
images. -/
public theorem listSum_hom {β : Type} (source : AdditiveCommutativeMonoidLaws α)
    (target : AdditiveCommutativeMonoidLaws β) (map : α → β)
    (mapZero : map source.zero = target.zero)
    (mapAdd : ∀ left right, map (source.add left right) = target.add (map left) (map right))
    (values : List α) :
    map (source.listSum values) = target.listSum (values.map map) := by
  induction values with
  | nil => exact mapZero
  | cons value values induction =>
      show map (source.add value (source.listSum values)) = target.add (map value) _
      rw [mapAdd, induction]

/-- A map that preserves zero and addition carries a sum of listed terms to the
sum of their images. -/
public theorem listSum_map_hom {β : Type} {ι : Type u}
    (source : AdditiveCommutativeMonoidLaws α) (target : AdditiveCommutativeMonoidLaws β)
    (map : α → β) (mapZero : map source.zero = target.zero)
    (mapAdd : ∀ left right, map (source.add left right) = target.add (map left) (map right))
    (indices : List ι) (values : ι → α) :
    map (source.listSum (indices.map values)) =
      target.listSum (indices.map fun index => map (values index)) := by
  rw [listSum_hom source target map mapZero mapAdd, List.map_map]
  rfl

/-- The sum of a vector: the leading entry plus the sum of the rest. -/
@[expose] public def finSum (laws : AdditiveCommutativeMonoidLaws α) :
    (dimension : Nat) → (Fin dimension → α) → α
  | 0, _ => laws.zero
  | dimension + 1, values =>
      laws.add (values 0) (finSum laws dimension (fun index => values index.succ))

public theorem finSum_zero (laws : AdditiveCommutativeMonoidLaws α) (values : Fin 0 → α) :
    laws.finSum 0 values = laws.zero :=
  rfl

public theorem finSum_succ (laws : AdditiveCommutativeMonoidLaws α) (dimension : Nat)
    (values : Fin (dimension + 1) → α) :
    laws.finSum (dimension + 1) values =
      laws.add (values 0) (laws.finSum dimension (fun index => values index.succ)) :=
  rfl

/-- A vector sums to the sum of its entries listed in index order. -/
public theorem finSum_eq_listSum (laws : AdditiveCommutativeMonoidLaws α) :
    (dimension : Nat) → (values : Fin dimension → α) →
      laws.finSum dimension values = laws.listSum ((List.finRange dimension).map values)
  | 0, _ => rfl
  | dimension + 1, values => by
      rw [finSum_succ, finSum_eq_listSum laws dimension, List.finRange_succ, List.map_cons,
        List.map_map]
      rfl

/-- Vectors that agree at every index have the same sum. -/
public theorem finSum_congr (laws : AdditiveCommutativeMonoidLaws α) (dimension : Nat)
    {left right : Fin dimension → α} (equal : ∀ index, left index = right index) :
    laws.finSum dimension left = laws.finSum dimension right :=
  congrArg (laws.finSum dimension) (funext equal)

/-- The zero vector sums to zero. -/
public theorem finSum_const_zero (laws : AdditiveCommutativeMonoidLaws α) :
    (dimension : Nat) → laws.finSum dimension (fun _ => laws.zero) = laws.zero
  | 0 => rfl
  | dimension + 1 => by
      rw [finSum_succ, finSum_const_zero laws dimension, laws.add_zero]

/-- The sum of a pointwise sum of vectors is the sum of the two sums. -/
public theorem finSum_add (laws : AdditiveCommutativeMonoidLaws α) (dimension : Nat)
    (left right : Fin dimension → α) :
    laws.finSum dimension (fun index => laws.add (left index) (right index)) =
      laws.add (laws.finSum dimension left) (laws.finSum dimension right) := by
  rw [finSum_eq_listSum, finSum_eq_listSum, finSum_eq_listSum]
  exact laws.listSum_map_add _ left right

/-- A vector that vanishes away from one index sums to that index's entry. -/
public theorem finSum_eq_single (laws : AdditiveCommutativeMonoidLaws α) :
    (dimension : Nat) → (values : Fin dimension → α) → (target : Fin dimension) →
      (∀ index, index ≠ target → values index = laws.zero) →
      laws.finSum dimension values = values target
  | 0, _, target, _ => target.elim0
  | dimension + 1, values, target, vanishing => by
      rw [finSum_succ]
      cases target using Fin.cases with
      | zero =>
          rw [laws.finSum_congr dimension (right := fun _ => laws.zero)
              (fun index => vanishing index.succ (Fin.succ_ne_zero index)),
            laws.finSum_const_zero dimension, laws.add_zero]
      | succ target =>
          rw [vanishing 0 (Fin.succ_ne_zero target).symm, laws.zero_add]
          exact laws.finSum_eq_single dimension (fun index => values index.succ) target
            (fun index different => vanishing index.succ
              (fun same => different (Fin.succ_inj.mp same)))

/-- A map that preserves zero and addition carries a vector's sum to the sum of
the images. -/
public theorem finSum_hom {β : Type} (source : AdditiveCommutativeMonoidLaws α)
    (target : AdditiveCommutativeMonoidLaws β) (map : α → β)
    (mapZero : map source.zero = target.zero)
    (mapAdd : ∀ left right, map (source.add left right) = target.add (map left) (map right)) :
    (dimension : Nat) → (values : Fin dimension → α) →
      map (source.finSum dimension values) =
        target.finSum dimension (fun index => map (values index))
  | 0, _ => mapZero
  | dimension + 1, values => by
      rw [finSum_succ, mapAdd, finSum_hom source target map mapZero mapAdd dimension]
      rfl

end AdditiveCommutativeMonoidLaws

namespace CommutativeSemiringLaws

variable {α : Type}

/-- A common left factor comes out of a sum. -/
public theorem listSum_map_mul_left (laws : CommutativeSemiringLaws α)
    {ι : Type u} (indices : List ι) (factor : α) (values : ι → α) :
    laws.additive.listSum (indices.map fun index => laws.multiplicative.mul factor (values index)) =
      laws.multiplicative.mul factor (laws.additive.listSum (indices.map values)) := by
  induction indices with
  | nil => exact (laws.mul_zero factor).symm
  | cons index indices induction =>
      show laws.additive.add (laws.multiplicative.mul factor (values index)) _ =
        laws.multiplicative.mul factor
          (laws.additive.add (values index) (laws.additive.listSum (indices.map values)))
      rw [induction, laws.mul_add]

/-- A common left factor comes out of a vector's sum. -/
public theorem finSum_mul_left (laws : CommutativeSemiringLaws α)
    (dimension : Nat) (factor : α) (values : Fin dimension → α) :
    laws.additive.finSum dimension (fun index => laws.multiplicative.mul factor (values index)) =
      laws.multiplicative.mul factor (laws.additive.finSum dimension values) := by
  rw [AdditiveCommutativeMonoidLaws.finSum_eq_listSum,
    AdditiveCommutativeMonoidLaws.finSum_eq_listSum]
  exact laws.listSum_map_mul_left _ factor values

end CommutativeSemiringLaws

end Problib.Algebra
