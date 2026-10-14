module

public import Problib.Measure.StandardBorel.Tree
public import Problib.Measure.StandardBorel.Real
public import Problib.QuasiBorel.Measurable.Tree

set_option autoImplicit false

/-!
# Tree examples

Binary trees with a real label at every node, and propositional formulas over
numbered variables. Both use only the generic tree theorems. Size and depth are
folds, so their recursion equations, measurability and morphisms come from the
fold's.
-/

namespace Problib.TreeExample

open Problib.Measure

/-- A leaf, or a branch with two children. Every node carries a real label. -/
abbrev binary : Signature where
  count := 2
  arity := fun label => 2 * label.val

/-- A variable, negation, conjunction and disjunction. -/
abbrev formula : Signature where
  count := 4
  arity := fun label => min label.val 2

/-- Only a variable carries a field, its number. -/
def FormulaField : Fin formula.count → Type
  | ⟨0, _⟩ => Nat
  | _ => Unit

def fieldCode : ∀ label, FormulaField label → Nat
  | ⟨0, _⟩, index => index
  | ⟨_ + 1, _⟩, _ => 0

theorem fieldCode_injective : ∀ label, Function.Injective (fieldCode label)
  | ⟨0, _⟩ => fun _ _ equal => equal
  | ⟨_ + 1, _⟩ => fun _ _ _ => rfl

section Folds

variable {signature : Signature} {Field : Fin signature.count → Type}

def size : Tree signature Field → Nat :=
  Tree.fold fun layer => 1 + (List.ofFn layer.2.2).sum

def depth : Tree signature Field → Nat :=
  Tree.fold fun layer => 1 + (List.ofFn layer.2.2).foldr max 0

example (layer : Tree.Layer signature Field (Tree signature Field)) :
    size (Tree.roll layer) = 1 + (List.ofFn fun index => size (layer.2.2 index)).sum :=
  Tree.fold_roll _ layer

example (layer : Tree.Layer signature Field (Tree signature Field)) :
    depth (Tree.roll layer) = 1 + (List.ofFn fun index => depth (layer.2.2 index)).foldr max 0 :=
  Tree.fold_roll _ layer

/-- Every map out of a finite tuple of naturals is measurable. -/
theorem tuple_measurable (length : Nat) (function : (Fin length → Nat) → Nat) :
    MeasurableMap (Space.pi fun _ : Fin length => Space.discrete Nat) (Space.discrete Nat) function := by
  intro region _
  have point : ∀ entries : Fin length → Nat,
      (Space.pi fun _ : Fin length => Space.discrete Nat).Measurable fun other => other = entries := by
    intro entries
    have differs := Space.i_union_of_nat_injection _ Fin.val (fun _ _ => Fin.ext) _ fun index =>
      Space.coordinate_measurable (fun _ : Fin length => Space.discrete Nat) index
        (Space.discrete_measurable fun value => ¬value = entries index)
    have equal : (fun other : Fin length → Nat => other = entries) =
        Set.complement fun other => ∃ index, ¬other index = entries index := by
      funext other
      apply propext
      constructor
      · rintro rfl ⟨index, differ⟩
        exact differ rfl
      · intro agree
        funext index
        exact Classical.byContradiction fun differ => agree ⟨index, differ⟩
    rw [equal]
    exact Space.complement _ differs
  have equal : Set.preimage function region =
      fun other => ∃ entries : {entries // region (function entries)}, other = entries.val := by
    funext other
    exact propext ⟨fun member => ⟨⟨other, member⟩, rfl⟩, fun ⟨entries, same⟩ => same ▸ entries.property⟩
  rw [equal]
  exact Space.i_union_of_nat_injection _ (fun entries => Countable.Pair.encodeTuple length entries.val)
    (fun _ _ same => Subtype.ext (Countable.Pair.encodeTuple_injective length same)) _
    fun entries => point entries.val

/-- A fold algebra that reads only the children's naturals is measurable. -/
theorem children_measurable (fields : ∀ label, Space (Field label))
    (combine : ∀ length, (Fin length → Nat) → Nat) :
    MeasurableMap (Space.product (Space.treeLayer fields (Space.discrete Nat)) (Space.discrete Unit))
      (Space.discrete Nat) fun input => combine _ input.1.2.2 := by
  have layered : MeasurableMap (Space.treeLayer fields (Space.discrete Nat)) (Space.discrete Nat)
      fun layer => combine _ layer.2.2 :=
    MeasurableMap.from_sigma_iff.mpr fun label =>
      MeasurableMap.comp (tuple_measurable (signature.arity label) (combine _))
        (Space.second_measurable (fields label)
          (Space.pi fun _ : Fin (signature.arity label) => Space.discrete Nat))
  intro region measurable
  exact Space.first_measurable _ _ (layered measurable)

theorem size_measurable (fields : ∀ label, Space (Field label)) :
    MeasurableMap (Space.tree fields) (Space.discrete Nat) size := by
  intro region measurable
  exact Space.pair_measurable (MeasurableMap.identity _) (MeasurableMap.constant _ _ ())
    (TreeSpace.fold_measurable fields
      (children_measurable fields fun _ children => 1 + (List.ofFn children).sum) measurable)

theorem depth_measurable (fields : ∀ label, Space (Field label)) :
    MeasurableMap (Space.tree fields) (Space.discrete Nat) depth := by
  intro region measurable
  exact Space.pair_measurable (MeasurableMap.identity _) (MeasurableMap.constant _ _ ())
    (TreeSpace.fold_measurable fields
      (children_measurable fields fun _ children => 1 + (List.ofFn children).foldr max 0) measurable)

end Folds

section QuasiBorel

open Problib.QuasiBorel

variable {Ω : Type} {source : Source Ω} {signature : Signature}

/-- Size as a quasi-Borel morphism, from the generic fold. -/
def sizeHom (fields : Fin signature.count → QuasiBorel.Space.{0, 0} source) :
    Hom (QuasiBorel.Space.product (QuasiBorel.Space.tree fields) (QuasiBorel.Space.terminal source))
      (QuasiBorel.Space.unrestricted source Nat) :=
  QuasiBorel.Space.treeFold fields
    { toFun := fun input => 1 + (List.ofFn input.1.2.2).sum, map_random := fun _ => trivial }

example (fields : Fin signature.count → QuasiBorel.Space.{0, 0} source)
    (tree : (QuasiBorel.Space.tree fields).Carrier) : sizeHom fields (tree, ()) = size tree := rfl

end QuasiBorel

/-- Real-labelled binary trees are standard Borel. -/
noncomputable example : StandardBorel (Space.tree (signature := binary) fun _ => Real.borel) :=
  StandardBorel.tree fun _ => StandardBorel.real

/-- Size is measurable on real-labelled binary trees. -/
example : MeasurableMap (Space.tree (signature := binary) fun _ => Real.borel) (Space.discrete Nat) size :=
  size_measurable _

/-- Formulas are countable. -/
example : Function.Injective (Tree.code (signature := formula) fieldCode) :=
  Tree.code_injective fieldCode_injective

/-- Formulas are standard Borel, from the same field codes. -/
noncomputable example : StandardBorel (Space.tree (signature := formula) fun label =>
    Space.discrete (FormulaField label)) :=
  StandardBorel.tree fun label => StandardBorel.ofNatInjection _ (fieldCode_injective label)

/-- `x₀ ∧ ¬x₁` has three connectives and variables on its longest path. -/
example :
    let variable_ := fun index : Nat =>
      (Tree.node (0 : Fin formula.count) (show FormulaField 0 from index) Fin.elim0 :
        Tree formula FormulaField)
    let negation := Tree.node (1 : Fin formula.count) (show FormulaField 1 from ())
      fun _ => variable_ 1
    let conjunction := Tree.node (2 : Fin formula.count) (show FormulaField 2 from ())
      fun index => if index.val = 0 then variable_ 0 else negation
    size conjunction = 4 ∧ depth conjunction = 3 := by
  decide

end Problib.TreeExample
