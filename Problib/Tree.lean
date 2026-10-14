module

public import Problib.Countable.Bijection

set_option autoImplicit false

/-!
# Finite trees over a signature

A signature lists the constructors of one recursive sort and the number of
children each takes. A tree node carries a constructor label, a field from that
constructor's field type, and its children. One layer of the signature functor
is `Σ label, Field label × (Fin (arity label) → X)`. Trees are its initial
algebra: `roll` and `unroll` are inverse, and `fold` is the unique algebra map.

A tree is determined by what it shows at each path of child indices. The
measurable and quasi-Borel spaces of trees are built from these observations,
and the shape of a tree, its labels without fields, partitions them countably.
-/

namespace Problib

public section

universe v w x

/-- The constructors of one recursive sort and the number of children each
takes. -/
structure Signature where
  count : Nat
  arity : Fin count → Nat

/-- Finite trees over a signature, with one field type per constructor. -/
inductive Tree (signature : Signature) (Field : Fin signature.count → Type v) : Type v where
  | node (label : Fin signature.count) (field : Field label)
      (children : Fin (signature.arity label) → Tree signature Field)

namespace Tree

variable {signature : Signature} {Field : Fin signature.count → Type v}

/-- One layer of the signature functor: a label, its field, and its children. -/
@[expose] def Layer (signature : Signature) (Field : Fin signature.count → Type v)
    (Child : Type w) : Type (max v w) :=
  Σ label, Field label × (Fin (signature.arity label) → Child)

/-- The functor's action: apply a function to every child of one layer. -/
@[expose] def Layer.map {Child : Type w} {Image : Type x} (function : Child → Image)
    (layer : Layer signature Field Child) : Layer signature Field Image :=
  ⟨layer.1, layer.2.1, fun index => function (layer.2.2 index)⟩

@[expose] def roll (layer : Layer signature Field (Tree signature Field)) : Tree signature Field :=
  node layer.1 layer.2.1 layer.2.2

@[expose] def unroll : Tree signature Field → Layer signature Field (Tree signature Field)
  | node label field children => ⟨label, field, children⟩

@[simp] theorem unroll_roll (layer : Layer signature Field (Tree signature Field)) :
    unroll (roll layer) = layer := rfl

@[simp] theorem roll_unroll (tree : Tree signature Field) : roll (unroll tree) = tree := by
  cases tree
  rfl

/-- Structural recursion: the algebra combines a node's field with the results
of its children. -/
@[expose] def fold {Result : Type w} (algebra : Layer signature Field Result → Result) :
    Tree signature Field → Result
  | node label field children => algebra ⟨label, field, fun index => fold algebra (children index)⟩

theorem fold_roll {Result : Type w} (algebra : Layer signature Field Result → Result)
    (layer : Layer signature Field (Tree signature Field)) :
    fold algebra (roll layer) = algebra (layer.map (fold algebra)) := rfl

/-- The label and field of the node at a path of child indices, or nothing when
the path leaves the tree. -/
@[expose] def observe : List Nat → Tree signature Field → Sum Unit (Σ label, Field label)
  | [], node label field _ => .inr ⟨label, field⟩
  | index :: path, node label _ children =>
      if bound : index < signature.arity label then observe path (children ⟨index, bound⟩)
      else .inl ()

/-- The label part of an observation. -/
@[expose] def observedLabel : Sum Unit (Σ label, Field label) → Option (Fin signature.count) :=
  Sum.elim (fun _ => none) (fun point => some point.1)

/-- Trees agreeing at every path are equal. -/
theorem observe_injective {left right : Tree signature Field}
    (agree : ∀ path, observe path left = observe path right) : left = right := by
  induction left generalizing right with
  | node label field children induction =>
      cases right with
      | node otherLabel otherField otherChildren =>
          obtain ⟨same, sameField⟩ := Sigma.mk.inj (Sum.inr.inj (agree []))
          subst same
          cases eq_of_heq sameField
          have sameChildren : children = otherChildren := by
            funext index
            apply induction index
            intro path
            have step := agree (index.val :: path)
            simp only [observe, index.isLt, dite_true] at step
            exact step
          rw [sameChildren]

/-- Trees with the fields forgotten. -/
abbrev Shape (signature : Signature) := Tree signature (fun _ => Unit)

@[expose] def shape : Tree signature Field → Shape signature :=
  fold fun layer => node layer.1 () layer.2.2

theorem observedLabel_shape (path : List Nat) (tree : Tree signature Field) :
    observedLabel (observe path (shape tree)) = observedLabel (observe path tree) := by
  induction tree generalizing path with
  | node label field children induction =>
      cases path with
      | nil => rfl
      | cons index path =>
          change observedLabel (dite _ (fun bound => observe path (shape (children ⟨index, bound⟩))) _) =
            observedLabel (dite _ (fun bound => observe path (children ⟨index, bound⟩)) _)
          split
          · exact induction _ path
          · rfl

/-- A tree has a given shape exactly when its labels agree with the shape's at
every path. -/
theorem shape_eq_iff (tree : Tree signature Field) (form : Shape signature) :
    shape tree = form ↔
      ∀ path, observedLabel (observe path tree) = observedLabel (observe path form) := by
  constructor
  · intro equal path
    rw [← equal, observedLabel_shape]
  · intro agree
    apply observe_injective
    intro path
    have same := (observedLabel_shape path tree).trans (agree path)
    revert same
    rcases observe path (shape tree) with _ | ⟨label, _⟩ <;>
      rcases observe path form with _ | ⟨other, _⟩ <;> simp [observedLabel]

/-- Observations whose labels follow some shape are the observations of a tree. -/
theorem exists_observe (form : Shape signature)
    (observation : List Nat → Sum Unit (Σ label, Field label))
    (agree : ∀ path, observedLabel (observation path) = observedLabel (observe path form)) :
    ∃ tree : Tree signature Field, ∀ path, observe path tree = observation path := by
  induction form generalizing observation with
  | node label _ children induction =>
      have root := agree []
      cases rooted : observation [] with
      | inl _ => rw [rooted] at root; cases root
      | inr point =>
          obtain ⟨otherLabel, field⟩ := point
          rw [rooted] at root
          cases Option.some.inj root
          have below := fun index : Fin (signature.arity label) =>
            induction index (fun path => observation (index.val :: path)) (fun path => by
              have step := agree (index.val :: path)
              simp only [observe, index.isLt, dite_true] at step
              exact step)
          refine ⟨node label field (fun index => Classical.choose (below index)), ?_⟩
          intro path
          cases path with
          | nil => exact rooted.symm
          | cons index path =>
              by_cases bound : index < signature.arity label
              · simp only [observe, bound, dite_true]
                exact Classical.choose_spec (below ⟨index, bound⟩) path
              · have step := agree (index :: path)
                simp only [observe, bound, dite_false] at step ⊢
                revert step
                cases observation (index :: path) <;> simp [observedLabel]

/-- A natural code of a tree from natural codes of its fields. -/
@[expose] def code (fieldCode : ∀ label, Field label → Nat) : Tree signature Field → Nat :=
  fold fun layer => Countable.Pair.encode (layer.1.val,
    Countable.Pair.encode (fieldCode layer.1 layer.2.1,
      Countable.Pair.encodeTuple _ layer.2.2)) + 1

/-- Trees are countable when every field type is. -/
theorem code_injective {fieldCode : ∀ label, Field label → Nat}
    (injective : ∀ label, Function.Injective (fieldCode label)) :
    Function.Injective (code fieldCode) := by
  intro left
  induction left with
  | node label field children induction =>
      intro right equal
      cases right with
      | node otherLabel otherField otherChildren =>
          obtain ⟨sameLabel, rest⟩ := Prod.mk.inj
            (Countable.Pair.encode_injective (Nat.succ.inj equal))
          cases Fin.ext sameLabel
          obtain ⟨sameField, sameChildren⟩ := Prod.mk.inj (Countable.Pair.encode_injective rest)
          cases injective label sameField
          have codes := Countable.Pair.encodeTuple_injective _ sameChildren
          have same : children = otherChildren :=
            funext fun index => induction index (congrFun codes index)
          rw [same]

/-- A child's code is below its parent's, for any field codes. -/
theorem code_child_lt (fieldCode : ∀ label, Field label → Nat) (label : Fin signature.count)
    (field : Field label) (children : Fin (signature.arity label) → Tree signature Field)
    (index : Fin (signature.arity label)) :
    code fieldCode (children index) < code fieldCode (node label field children) := by
  have entry := Countable.Pair.le_encodeTuple _ (fun index => code fieldCode (children index)) index
  have inner := (Countable.Pair.le_encode (fieldCode label field,
    Countable.Pair.encodeTuple _ (fun index => code fieldCode (children index)))).2
  have outer := (Countable.Pair.le_encode (label.val, Countable.Pair.encode (fieldCode label field,
    Countable.Pair.encodeTuple _ (fun index => code fieldCode (children index))))).2
  show _ < Countable.Pair.encode (label.val, Countable.Pair.encode (fieldCode label field,
    Countable.Pair.encodeTuple _ (fun index => code fieldCode (children index)))) + 1
  omega

/-- The code of a tree's shape, a rank that falls from parent to child. -/
@[expose] def rank (tree : Tree signature Field) : Nat :=
  code (fun _ _ => 0) (shape tree)

theorem rank_child_lt (label : Fin signature.count) (field : Field label)
    (children : Fin (signature.arity label) → Tree signature Field)
    (index : Fin (signature.arity label)) :
    rank (children index) < rank (node label field children) :=
  code_child_lt (Field := fun _ => Unit) _ label () (fun index => shape (children index)) index

end Tree

end

end Problib
