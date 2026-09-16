module

public import Foundations.Real.Construction.Dedekind.Selection

namespace Foundations.Real.Construction.Dedekind

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

public theorem subEqAddNeg (left right : selection.Carrier) :
    sub left right = add left (neg right) :=
  additive.group.subEqAddNeg left right

public theorem addComm (left right : selection.Carrier) :
    add left right = add right left :=
  additive.group.add_comm left right

public theorem addAssoc (left middle right : selection.Carrier) :
    add (add left middle) right = add left (add middle right) :=
  additive.group.add_assoc left middle right

public theorem addLeftComm (left middle right : selection.Carrier) :
    add left (add middle right) = add middle (add left right) :=
  Foundations.Algebra.AdditiveCommutativeGroupLaws.addLeftComm
    additive.group left middle right

public theorem addZero (value : selection.Carrier) :
    add value zero = value :=
  additive.group.add_zero value

public theorem addNeg (value : selection.Carrier) :
    add value (neg value) = zero :=
  additive.group.add_neg value

public theorem addLeftCancel {left first second : selection.Carrier}
    (equal : add left first = add left second) : first = second :=
  Foundations.Algebra.AdditiveCommutativeGroupLaws.addLeftCancel
    additive.group equal

public theorem addRightCancel {right first second : selection.Carrier}
    (equal : add first right = add second right) : first = second :=
  Foundations.Algebra.AdditiveCommutativeGroupLaws.addRightCancel
    additive.group equal

public theorem ofRatZero : selection.ofRat 0 = zero :=
  RationalAdditiveHomomorphism.mapZero
    additive.group selection.ofRat additive.rational

public theorem ofRatAdd (left right : Rat) :
    selection.ofRat (left + right) =
      add (selection.ofRat left) (selection.ofRat right) :=
  additive.rational.map_add left right

public theorem ofRatNeg (value : Rat) :
    selection.ofRat (-value) = neg (selection.ofRat value) :=
  RationalAdditiveHomomorphism.mapNeg
    additive.group selection.ofRat additive.rational value

public theorem ofRatSub (left right : Rat) :
    selection.ofRat (left - right) =
      sub (selection.ofRat left) (selection.ofRat right) :=
  RationalAdditiveHomomorphism.mapSub
    additive.group selection.ofRat additive.rational left right

public theorem addLeAddRightIff {left right shift : selection.Carrier} :
    le (add left shift) (add right shift) ↔ le left right :=
  by
    simpa only [AdditiveOrderExtension.orderedGroup, le, add] using
      additive.orderedGroup.addLeAddRightIff

public theorem addLeAddLeftIff {left right shift : selection.Carrier} :
    le (add shift left) (add shift right) ↔ le left right :=
  by
    simpa only [AdditiveOrderExtension.orderedGroup, le, add] using
      additive.orderedGroup.addLeAddLeftIff

public theorem addLtAddRightIff {left right shift : selection.Carrier} :
    lt (add left shift) (add right shift) ↔ lt left right := by
  unfold lt
  rw [addLeAddRightIff, addLeAddRightIff]

public theorem addLtAddLeftIff {left right shift : selection.Carrier} :
    lt (add shift left) (add shift right) ↔ lt left right := by
  unfold lt
  rw [addLeAddLeftIff, addLeAddLeftIff]

public theorem negLeNegIff {left right : selection.Carrier} :
    le (neg right) (neg left) ↔ le left right :=
  by
    simpa only [AdditiveOrderExtension.orderedGroup, le, neg] using
      additive.orderedGroup.negLeNegIff

public theorem negLtNegIff {left right : selection.Carrier} :
    lt (neg right) (neg left) ↔ lt left right := by
  unfold lt
  rw [negLeNegIff, negLeNegIff]

end Foundations.Real.Construction.Dedekind
