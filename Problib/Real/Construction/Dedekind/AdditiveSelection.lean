module

public import Problib.Real.Construction.Dedekind.Selection

namespace Problib.Real.Construction.Dedekind

@[expose] public def additiveSelection : AdditiveSelection where
  ordered := selection
  additive := additive

@[expose] public def zero : selection.Carrier :=
  additive.group.zero

@[expose] public def add (left right : selection.Carrier) : selection.Carrier :=
  additive.group.add left right

@[expose] public def neg (value : selection.Carrier) : selection.Carrier :=
  additive.group.neg value

@[expose] public def sub (left right : selection.Carrier) : selection.Carrier :=
  additive.group.sub left right

public theorem sub_eq_add_neg (left right : selection.Carrier) :
    sub left right = add left (neg right) :=
  additive.group.sub_eq_add_neg left right

public theorem add_comm (left right : selection.Carrier) :
    add left right = add right left :=
  additive.group.add_comm left right

public theorem add_assoc (left middle right : selection.Carrier) :
    add (add left middle) right = add left (add middle right) :=
  additive.group.add_assoc left middle right

public theorem add_left_comm (left middle right : selection.Carrier) :
    add left (add middle right) = add middle (add left right) :=
  Problib.Algebra.AdditiveCommutativeGroupLaws.add_left_comm
    additive.group left middle right

public theorem add_zero (value : selection.Carrier) :
    add value zero = value :=
  additive.group.add_zero value

public theorem add_neg (value : selection.Carrier) :
    add value (neg value) = zero :=
  additive.group.add_neg value

public theorem add_left_cancel {left first second : selection.Carrier}
    (equal : add left first = add left second) : first = second :=
  Problib.Algebra.AdditiveCommutativeGroupLaws.add_left_cancel
    additive.group equal

public theorem add_right_cancel {right first second : selection.Carrier}
    (equal : add first right = add second right) : first = second :=
  Problib.Algebra.AdditiveCommutativeGroupLaws.add_right_cancel
    additive.group equal

public theorem ofRat_zero : selection.ofRat 0 = zero :=
  RationalAdditiveHomomorphism.map_zero
    additive.group selection.ofRat additive.rational

public theorem ofRat_add (left right : Rat) :
    selection.ofRat (left + right) =
      add (selection.ofRat left) (selection.ofRat right) :=
  additive.rational.map_add left right

public theorem ofRat_neg (value : Rat) :
    selection.ofRat (-value) = neg (selection.ofRat value) :=
  RationalAdditiveHomomorphism.map_neg
    additive.group selection.ofRat additive.rational value

public theorem ofRat_sub (left right : Rat) :
    selection.ofRat (left - right) =
      sub (selection.ofRat left) (selection.ofRat right) :=
  RationalAdditiveHomomorphism.map_sub
    additive.group selection.ofRat additive.rational left right

public theorem add_le_add_right_iff {left right shift : selection.Carrier} :
    le (add left shift) (add right shift) ↔ le left right :=
  by
    simpa only [AdditiveOrderExtension.orderedGroup, le, add] using
      additive.orderedGroup.add_le_add_right_iff

public theorem add_le_add_left_iff {left right shift : selection.Carrier} :
    le (add shift left) (add shift right) ↔ le left right :=
  by
    simpa only [AdditiveOrderExtension.orderedGroup, le, add] using
      additive.orderedGroup.add_le_add_left_iff

public theorem add_lt_add_right_iff {left right shift : selection.Carrier} :
    lt (add left shift) (add right shift) ↔ lt left right := by
  unfold lt
  rw [add_le_add_right_iff, add_le_add_right_iff]

public theorem add_lt_add_left_iff {left right shift : selection.Carrier} :
    lt (add shift left) (add shift right) ↔ lt left right := by
  unfold lt
  rw [add_le_add_left_iff, add_le_add_left_iff]

public theorem neg_le_neg_iff {left right : selection.Carrier} :
    le (neg right) (neg left) ↔ le left right :=
  by
    simpa only [AdditiveOrderExtension.orderedGroup, le, neg] using
      additive.orderedGroup.neg_le_neg_iff

public theorem neg_lt_neg_iff {left right : selection.Carrier} :
    lt (neg right) (neg left) ↔ lt left right := by
  unfold lt
  rw [neg_le_neg_iff, neg_le_neg_iff]

end Problib.Real.Construction.Dedekind
