module

public import Problib.Real.Arithmetic

/-! Opt-in `grind` algebra for the selected real carrier.

Real algebra in problib is stated through explicit operations on
`selection.Carrier`, so a proof that only reassociates, distributes, or moves
summands across an inequality has to spell every step as a rewrite. Core `grind`
decides commutative-ring equalities and linear order over any type with
`Lean.Grind` instances. This module gives the carrier those instances, built
from the proved laws: `CommRing`, `Field` (with `inverse zero = zero` as the
junk value), `IsCharP _ 0`, the linear order classes, and `OrderedRing`. Numerals
and casts go through `selection.ofRat`, so `selection.ofRat 2` and the numeral
`2` agree by `rfl`. Every field is satisfied.

The instances are scoped to `Problib.Real.Grind`. A file that never opens the
namespace keeps the explicit interface of the Real boundary: no `+`, `*`, or
`≤` resolves on the carrier, and public statements keep their explicit form.
The `real_grind` tactic opens the namespace for one call. It rewrites the
explicit operations to notation by the `rfl` bridges below and runs `grind`.
-/

set_option autoImplicit false

namespace Problib.Real.Grind

open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Operations, numerals and powers -/

public scoped instance : Add selection.Carrier := ⟨add⟩
public scoped instance : Mul selection.Carrier := ⟨mul⟩
public scoped instance : Neg selection.Carrier := ⟨neg⟩
public scoped instance : Sub selection.Carrier := ⟨sub⟩
public scoped instance : Inv selection.Carrier := ⟨inverse⟩
public scoped instance : Div selection.Carrier := ⟨div⟩
public scoped instance : LE selection.Carrier := ⟨le⟩
public scoped instance : LT selection.Carrier := ⟨lt⟩
public scoped instance : NatCast selection.Carrier :=
  ⟨fun index => selection.ofRat index⟩
public scoped instance : IntCast selection.Carrier :=
  ⟨fun index => selection.ofRat index⟩
public scoped instance (index : Nat) : OfNat selection.Carrier index :=
  ⟨selection.ofRat index⟩
public scoped instance : SMul Nat selection.Carrier :=
  ⟨fun index value => mul (selection.ofRat index) value⟩
public scoped instance : SMul Int selection.Carrier :=
  ⟨fun index value => mul (selection.ofRat index) value⟩
public scoped instance : HPow selection.Carrier Nat selection.Carrier :=
  ⟨fun value index => Nat.rec one (fun _ product => mul product value) index⟩
public scoped instance : HPow selection.Carrier Int selection.Carrier :=
  ⟨fun value index => Int.rec (fun count => value ^ count)
    (fun count => inverse (value ^ (count + 1))) index⟩

/-! ### Algebraic and order structure -/

public theorem zero_eq : zero = (0 : selection.Carrier) := ofRat_zero.symm

public theorem one_eq : one = (1 : selection.Carrier) := ofRat_one.symm

public scoped instance commRing : Lean.Grind.CommRing selection.Carrier where
  add_zero value := by rw [← zero_eq]; exact add_zero value
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_one value := by rw [← one_eq]; exact mul_one value
  one_mul value := by rw [← one_eq]; exact one_mul value
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul value := by rw [← zero_eq]; exact zero_mul value
  mul_zero value := by rw [← zero_eq]; exact mul_zero value
  mul_comm := mul_comm
  pow_zero _ := one_eq
  pow_succ _ _ := rfl
  ofNat_succ index := by
    show selection.ofRat ((index + 1 : Nat) : Rat) =
      add (selection.ofRat (index : Rat)) (selection.ofRat ((1 : Nat) : Rat))
    rw [Rat.natCast_add, ofRat_add]
  neg_add_cancel value := by
    rw [← zero_eq]
    exact (add_comm _ _).trans (add_neg value)
  sub_eq_add_neg := sub_eq_add_neg
  neg_zsmul index value := by
    show mul (selection.ofRat ((-index : Int) : Rat)) value =
      neg (mul (selection.ofRat (index : Rat)) value)
    rw [Rat.intCast_neg, ofRat_neg, neg_mul]
  intCast_neg index := by
    show selection.ofRat ((-index : Int) : Rat) = neg (selection.ofRat (index : Rat))
    rw [Rat.intCast_neg, ofRat_neg]

public scoped instance field : Lean.Grind.Field selection.Carrier where
  div_eq_mul_inv := div_eq_mul_inverse
  zero_ne_one := by
    rw [← zero_eq, ← one_eq]
    exact fun equal => one_ne_zero equal.symm
  inv_zero := by rw [← zero_eq]; exact inverse_zero
  mul_inv_cancel {value} nonzero := by
    rw [← zero_eq] at nonzero
    rw [← one_eq]
    exact mul_inverse_cancel nonzero
  zpow_zero _ := one_eq
  zpow_succ _ _ := rfl
  zpow_neg value index := by
    rcases index with (_ | count) | count
    · show one = inverse one
      exact inverse_one.symm
    · rfl
    · exact (inverse_inverse _).symm

public scoped instance characteristic : Lean.Grind.IsCharP selection.Carrier 0 where
  ofNat_ext_iff {left right} := by
    show selection.ofRat (left : Rat) = selection.ofRat (right : Rat) ↔ _
    rw [Nat.mod_zero, Nat.mod_zero]
    exact ⟨fun equal => Rat.natCast_inj.mp (ofRat_injective equal),
      fun equal => by rw [equal]⟩

public scoped instance linearOrder : Std.IsLinearOrder selection.Carrier where
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total := le_total

public scoped instance lawfulLT : Std.LawfulOrderLT selection.Carrier where
  lt_iff _ _ := Iff.rfl

public scoped instance orderedRing : Lean.Grind.OrderedRing selection.Carrier where
  add_le_left_iff shift := add_le_add_right_iff.symm
  zero_lt_one := by
    rw [← zero_eq, ← one_eq]
    exact one_positive
  mul_lt_mul_of_pos_left less positive := by
    rw [← zero_eq] at positive
    exact mul_lt_mul_positive_left less positive
  mul_lt_mul_of_pos_right less positive := by
    rw [← zero_eq] at positive
    exact mul_lt_mul_positive_right less positive

/-! ### Bridges from the explicit operations to notation -/

public theorem add_eq (left right : selection.Carrier) :
    add left right = left + right := rfl

public theorem mul_eq (left right : selection.Carrier) :
    mul left right = left * right := rfl

public theorem neg_eq (value : selection.Carrier) : neg value = -value := rfl

public theorem sub_eq (left right : selection.Carrier) :
    sub left right = left - right := rfl

public theorem inverse_eq (value : selection.Carrier) :
    inverse value = value⁻¹ := rfl

public theorem div_eq (left right : selection.Carrier) :
    div left right = left / right := rfl

public theorem le_eq (left right : selection.Carrier) :
    le left right = (left ≤ right) := rfl

public theorem lt_eq (left right : selection.Carrier) :
    lt left right = (left < right) := rfl

public theorem ofRat_ofNat (index : Nat) :
    selection.ofRat (no_index (OfNat.ofNat index)) =
      (OfNat.ofNat index : selection.Carrier) := rfl

end

end Problib.Real.Grind

/-- `real_grind` closes a goal about the selected real carrier stated through
the explicit operations. It rewrites `add`, `mul`, `neg`, `sub`, `inverse`,
`div`, `le`, `lt`, `zero`, `one` and numeral `ofRat` in the goal and every
hypothesis to notation, then runs `grind` with the scoped instances of
`Problib.Real.Grind` open. Optional `grind` parameters pass through. -/
syntax (name := realGrind) "real_grind"
  (" [" withoutPosition(Lean.Parser.Tactic.grindParam,*) "]")? : tactic

macro_rules
  | `(tactic| real_grind $[[$params,*]]?) => `(tactic|
      open scoped Problib.Real.Grind in
      ((try simp only [Problib.Real.Grind.add_eq, Problib.Real.Grind.mul_eq,
          Problib.Real.Grind.neg_eq, Problib.Real.Grind.sub_eq,
          Problib.Real.Grind.inverse_eq, Problib.Real.Grind.div_eq,
          Problib.Real.Grind.le_eq, Problib.Real.Grind.lt_eq,
          Problib.Real.Grind.zero_eq, Problib.Real.Grind.one_eq,
          Problib.Real.Grind.ofRat_ofNat] at *) <;>
       grind $[[$params,*]]?))
