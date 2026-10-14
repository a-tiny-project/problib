module

public import Problib.Algebra.Sum

/-! Finite products over multiplicative commutative monoid laws.

`toAdditive` reads multiplicative laws as additive ones, with one as zero and
multiplication as addition. `listProduct` and `finProduct` are the sums at those
laws, so each product lemma here is a sum lemma at `toAdditive`. The successor
split `finProduct (n + 1) f = f 0 * finProduct n (fun i => f i.succ)` holds by
`rfl`.
-/

set_option autoImplicit false

namespace Problib.Algebra

universe u

namespace MultiplicativeCommutativeMonoidLaws

variable {α : Type}

/-- Multiplicative laws read as additive laws: one is zero, and multiplication is
addition. -/
@[expose, reducible] public def toAdditive (laws : MultiplicativeCommutativeMonoidLaws α) :
    AdditiveCommutativeMonoidLaws α where
  zero := laws.one
  add := laws.mul
  add_comm := laws.mul_comm
  add_assoc := laws.mul_assoc
  add_zero := laws.mul_one

/-- The product of a list. -/
@[expose] public def listProduct (laws : MultiplicativeCommutativeMonoidLaws α)
    (values : List α) : α :=
  laws.toAdditive.listSum values

/-- The product of a vector: the leading entry times the product of the rest. -/
@[expose] public def finProduct (laws : MultiplicativeCommutativeMonoidLaws α)
    (dimension : Nat) (values : Fin dimension → α) : α :=
  laws.toAdditive.finSum dimension values

public theorem listProduct_nil (laws : MultiplicativeCommutativeMonoidLaws α) :
    laws.listProduct [] = laws.one :=
  rfl

public theorem listProduct_cons (laws : MultiplicativeCommutativeMonoidLaws α)
    (value : α) (values : List α) :
    laws.listProduct (value :: values) = laws.mul value (laws.listProduct values) :=
  rfl

public theorem listProduct_append (laws : MultiplicativeCommutativeMonoidLaws α)
    (left right : List α) :
    laws.listProduct (left ++ right) =
      laws.mul (laws.listProduct left) (laws.listProduct right) :=
  laws.toAdditive.listSum_append left right

public theorem listProduct_perm (laws : MultiplicativeCommutativeMonoidLaws α)
    {left right : List α} (permutation : left.Perm right) :
    laws.listProduct left = laws.listProduct right :=
  laws.toAdditive.listSum_perm permutation

public theorem listProduct_map_mul (laws : MultiplicativeCommutativeMonoidLaws α)
    {ι : Type u} (indices : List ι) (left right : ι → α) :
    laws.listProduct (indices.map fun index => laws.mul (left index) (right index)) =
      laws.mul (laws.listProduct (indices.map left)) (laws.listProduct (indices.map right)) :=
  laws.toAdditive.listSum_map_add indices left right

/-- A product whose every listed factor is one is one. -/
public theorem listProduct_map_eq_one (laws : MultiplicativeCommutativeMonoidLaws α)
    {ι : Type u} (indices : List ι) (values : ι → α)
    (unit : ∀ index, index ∈ indices → values index = laws.one) :
    laws.listProduct (indices.map values) = laws.one :=
  laws.toAdditive.listSum_map_eq_zero indices values unit

public theorem finProduct_zero (laws : MultiplicativeCommutativeMonoidLaws α)
    (values : Fin 0 → α) :
    laws.finProduct 0 values = laws.one :=
  rfl

public theorem finProduct_succ (laws : MultiplicativeCommutativeMonoidLaws α)
    (dimension : Nat) (values : Fin (dimension + 1) → α) :
    laws.finProduct (dimension + 1) values =
      laws.mul (values 0) (laws.finProduct dimension (fun index => values index.succ)) :=
  rfl

public theorem finProduct_eq_listProduct (laws : MultiplicativeCommutativeMonoidLaws α)
    (dimension : Nat) (values : Fin dimension → α) :
    laws.finProduct dimension values =
      laws.listProduct ((List.finRange dimension).map values) :=
  laws.toAdditive.finSum_eq_listSum dimension values

public theorem finProduct_congr (laws : MultiplicativeCommutativeMonoidLaws α)
    (dimension : Nat) {left right : Fin dimension → α}
    (equal : ∀ index, left index = right index) :
    laws.finProduct dimension left = laws.finProduct dimension right :=
  laws.toAdditive.finSum_congr dimension equal

public theorem finProduct_const_one (laws : MultiplicativeCommutativeMonoidLaws α)
    (dimension : Nat) :
    laws.finProduct dimension (fun _ => laws.one) = laws.one :=
  laws.toAdditive.finSum_const_zero dimension

public theorem finProduct_mul (laws : MultiplicativeCommutativeMonoidLaws α)
    (dimension : Nat) (left right : Fin dimension → α) :
    laws.finProduct dimension (fun index => laws.mul (left index) (right index)) =
      laws.mul (laws.finProduct dimension left) (laws.finProduct dimension right) :=
  laws.toAdditive.finSum_add dimension left right

public theorem finProduct_eq_single (laws : MultiplicativeCommutativeMonoidLaws α)
    (dimension : Nat) (values : Fin dimension → α) (target : Fin dimension)
    (unit : ∀ index, index ≠ target → values index = laws.one) :
    laws.finProduct dimension values = values target :=
  laws.toAdditive.finSum_eq_single dimension values target unit

public theorem finProduct_hom {β : Type} (source : MultiplicativeCommutativeMonoidLaws α)
    (target : MultiplicativeCommutativeMonoidLaws β) (map : α → β)
    (mapOne : map source.one = target.one)
    (mapMul : ∀ left right, map (source.mul left right) = target.mul (map left) (map right))
    (dimension : Nat) (values : Fin dimension → α) :
    map (source.finProduct dimension values) =
      target.finProduct dimension (fun index => map (values index)) :=
  AdditiveCommutativeMonoidLaws.finSum_hom source.toAdditive target.toAdditive map mapOne mapMul
    dimension values

end MultiplicativeCommutativeMonoidLaws

end Problib.Algebra
