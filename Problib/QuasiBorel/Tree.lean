module

public import Problib.Tree
public import Problib.QuasiBorel.Sum
public import Problib.QuasiBorel.Pi
public import Problib.QuasiBorel.CartesianClosed

set_option autoImplicit false

/-!
# Quasi-Borel finite trees

Random trees are built node by node, from a correlated field and correlated
children, and closed under reparameterization and countable gluing, as random
lists are. Roll and unroll are inverse morphisms against one layer of the
signature functor, and a fold with an algebra morphism is a morphism that
satisfies the fold equation.
-/

namespace Problib.QuasiBorel

public section

universe u v w

variable {Ω : Type u} {source : Source Ω} {signature : Signature}

/-- Finite tree random elements. A node combines a random field with random
children, all correlated through the shared seed. -/
inductive TreeRandom (fields : Fin signature.count → Space.{u, v} source) :
    (Ω → Tree signature fun label => (fields label).Carrier) → Prop where
  | node (label : Fin signature.count) {field : Ω → (fields label).Carrier}
      {children : Fin (signature.arity label) → Ω → Tree signature fun label => (fields label).Carrier} :
      (fields label).Random field →
      (∀ index, TreeRandom fields (children index)) →
      TreeRandom fields (fun seed => .node label (field seed) (fun index => children index seed))
  | reparam {parameter random} : source.Measurable parameter →
      TreeRandom fields random → TreeRandom fields (fun seed => random (parameter seed))
  | piecewise {partition : Ω → Nat}
      {branches : Nat → Ω → Tree signature fun label => (fields label).Carrier} :
      source.Partition partition → (∀ index, TreeRandom fields (branches index)) →
      TreeRandom fields (fun seed => branches (partition seed) seed)

namespace Space

@[expose] def tree (fields : Fin signature.count → Space.{u, v} source) : Space source where
  Carrier := Tree signature fun label => (fields label).Carrier
  Random := TreeRandom fields
  constant := by
    intro tree
    induction tree with
    | node label field _ induction => exact .node label ((fields label).constant field) induction
  reparam := TreeRandom.reparam
  piecewise := TreeRandom.piecewise

/-- One layer of the signature functor over a space of children. -/
@[expose, reducible] def treeLayer (fields : Fin signature.count → Space.{u, v} source)
    (children : Space.{u, w} source) : Space source :=
  sigma fun label => product (fields label) (pi fun _ : Fin (signature.arity label) => children)

@[expose] def treeRoll (fields : Fin signature.count → Space.{u, v} source) :
    Hom (treeLayer fields (tree fields)) (tree fields) where
  toFun := Tree.roll
  map_random := by
    intro random accepted
    induction accepted with
    | mk label accepted => exact .node label accepted.1 accepted.2
    | reparam measurable _ induction => exact .reparam measurable induction
    | piecewise measurable _ induction => exact .piecewise measurable induction

@[expose] def treeUnroll (fields : Fin signature.count → Space.{u, v} source) :
    Hom (tree fields) (treeLayer fields (tree fields)) where
  toFun := Tree.unroll
  map_random := by
    intro random accepted
    induction accepted with
    | node label field children => exact SigmaRandom.mk label ⟨field, children⟩
    | reparam measurable _ induction => exact SigmaRandom.reparam measurable induction
    | piecewise measurable _ induction => exact SigmaRandom.piecewise measurable induction

theorem treeUnroll_treeRoll (fields : Fin signature.count → Space.{u, v} source) :
    Hom.comp (treeUnroll fields) (treeRoll fields) = Hom.identity _ :=
  Hom.ext fun _ => rfl

theorem treeRoll_treeUnroll (fields : Fin signature.count → Space.{u, v} source) :
    Hom.comp (treeRoll fields) (treeUnroll fields) = Hom.identity _ :=
  Hom.ext Tree.roll_unroll

/-- Apply a morphism with a shared parameter to every child of one layer. -/
@[expose] def treeLayerMapAt (fields : Fin signature.count → Space.{u, v} source)
    {children images parameter : Space source} (morphism : Hom (product children parameter) images)
    (layer : Tree.Layer signature (fun label => (fields label).Carrier) children.Carrier) :
    Hom parameter (treeLayer fields images) where
  toFun := fun captured => layer.map fun child => morphism (child, captured)
  map_random := fun accepted => SigmaRandom.mk layer.1 ⟨(fields layer.1).constant layer.2.1,
    fun index => morphism.map_random ⟨children.constant (layer.2.2 index), accepted⟩⟩

/-- The functor's action on a morphism that shares a parameter with the layer. -/
@[expose] def treeLayerMap (fields : Fin signature.count → Space.{u, v} source)
    {children images parameter : Space source} (morphism : Hom (product children parameter) images) :
    Hom (product (treeLayer fields children) parameter) (treeLayer fields images) :=
  uncurry {
    toFun := treeLayerMapAt fields morphism
    map_random := by
      intro random accepted
      induction accepted with
      | mk label accepted =>
          intro randomPair valid
          exact SigmaRandom.mk label ⟨(fields label).reparam valid.1 accepted.1,
            fun index => morphism.map_random ⟨children.reparam valid.1 (accepted.2 index), valid.2⟩⟩
      | @reparam mapping random measurable _ induction =>
          exact (exponential parameter (treeLayer fields images)).reparam
            (random := fun seed => treeLayerMapAt fields morphism (random seed)) measurable induction
      | piecewise measurable _ induction =>
          exact (exponential parameter (treeLayer fields images)).piecewise measurable induction }

/-- Fold one tree into a morphism out of the algebra's shared parameter. -/
@[expose] def treeFoldAt (fields : Fin signature.count → Space.{u, v} source)
    {result parameter : Space source} (algebra : Hom (product (treeLayer fields result) parameter) result)
    (tree : (tree fields).Carrier) : Hom parameter result where
  toFun := fun captured => Tree.fold (fun layer => algebra (layer, captured)) tree
  map_random := by
    induction tree with
    | node label field _ induction =>
        intro random accepted
        exact algebra.map_random ⟨SigmaRandom.mk label
          ⟨(fields label).constant field, fun index => induction index accepted⟩, accepted⟩

/-- Fold a tree with an algebra that may share parameters with it. -/
@[expose] def treeFold (fields : Fin signature.count → Space.{u, v} source)
    {result parameter : Space source} (algebra : Hom (product (treeLayer fields result) parameter) result) :
    Hom (product (tree fields) parameter) result :=
  uncurry {
    toFun := treeFoldAt fields algebra
    map_random := by
      intro random accepted
      induction accepted with
      | node label field _ induction =>
          intro randomPair valid
          exact algebra.map_random ⟨SigmaRandom.mk label
            ⟨(fields label).reparam valid.1 field, fun index => induction index valid⟩, valid.2⟩
      | @reparam mapping random measurable _ induction =>
          exact (exponential parameter result).reparam
            (random := fun seed => treeFoldAt fields algebra (random seed)) measurable induction
      | piecewise measurable _ induction =>
          exact (exponential parameter result).piecewise measurable induction }

@[simp] theorem treeFold_apply (fields : Fin signature.count → Space.{u, v} source)
    {result parameter : Space source} (algebra : Hom (product (treeLayer fields result) parameter) result)
    (tree : (tree fields).Carrier) (captured : parameter.Carrier) :
    treeFold fields algebra (tree, captured) = Tree.fold (fun layer => algebra (layer, captured)) tree :=
  rfl

/-- Folding a rolled layer applies the algebra to the layer's folded children. -/
theorem treeFold_treeRoll (fields : Fin signature.count → Space.{u, v} source)
    {result parameter : Space source} (algebra : Hom (product (treeLayer fields result) parameter) result) :
    Hom.comp (treeFold fields algebra) (productMap (treeRoll fields) (Hom.identity parameter)) =
      Hom.comp algebra (pair (treeLayerMap fields (treeFold fields algebra)) (second _ _)) :=
  Hom.ext fun _ => rfl

end Space

end

end Problib.QuasiBorel
