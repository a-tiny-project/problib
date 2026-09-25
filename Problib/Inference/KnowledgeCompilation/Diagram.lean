module

public import Problib.Inference.KnowledgeCompilation.Circuit

namespace Problib.Inference.KnowledgeCompilation
public section

/-- A decision node. References zero and one denote the Boolean terminals. -/
structure Node where
  key : Nat
  low : Nat
  high : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Node at array position n has reference n + 2. -/
structure Diagram where
  nodes : Array Node
  deriving Repr, Inhabited

/-- Read a nonterminal reference without conflating either terminal with a node. -/
@[expose] def Diagram.node? (diagram : Diagram) : Nat → Option Node
  | 0 | 1 => none
  | index + 2 => diagram.nodes[index]?

/-- Total Boolean interpretation of an untrusted diagram. -/
@[expose] def Diagram.eval (diagram : Diagram) (assignment : Nat → Bool) (reference : Nat) : Bool :=
  match reference with
  | 0 => false
  | 1 => true
  | index + 2 =>
      match diagram.nodes[index]? with
      | none => false
      | some node =>
          if _bound : node.low < index + 2 ∧ node.high < index + 2 then
            if assignment node.key then diagram.eval assignment node.high
            else diagram.eval assignment node.low
          else false
termination_by reference

/-- Peel a root decision on one key. An unrelated root stays unchanged. -/
@[expose] def Diagram.cofactor (diagram : Diagram) (reference key : Nat) (branch : Bool) : Nat :=
  match diagram.node? reference with
  | none => reference
  | some node =>
      if node.key = key ∧ node.low < reference ∧ node.high < reference then
        if branch then node.high else node.low
      else reference

/-- Root cofactoring preserves interpretation for the selected assignment branch. -/
theorem Diagram.eval_cofactor (diagram : Diagram) (assignment : Nat → Bool)
    (reference key : Nat) :
    diagram.eval assignment (diagram.cofactor reference key (assignment key)) =
      diagram.eval assignment reference := by
  cases reference with
  | zero => simp [cofactor, node?]
  | succ reference =>
      cases reference with
      | zero => simp [cofactor, node?]
      | succ index =>
          simp only [cofactor, node?]
          split
          · rfl
          · rename_i node found
            split
            · rename_i conditions
              rcases conditions with ⟨same, low, high⟩
              rw [eval]
              have bounds : node.low < index + 2 ∧ node.high < index + 2 := ⟨low, high⟩
              simp only [found, dif_pos bounds, same]
              cases assignment key <;> rfl
            · rfl

/-- The canonical decision node realizes its named input variable. -/
theorem Diagram.eval_variable (diagram : Diagram) (assignment : Nat → Bool)
    (reference key : Nat) (found : diagram.node? reference = some ⟨key, 0, 1⟩) :
    diagram.eval assignment reference = assignment key := by
  cases reference with
  | zero => simp [node?] at found
  | succ reference =>
      cases reference with
      | zero => simp [node?] at found
      | succ index =>
          change diagram.nodes[index]? = some ⟨key, 0, 1⟩ at found
          rw [eval]
          simp only [found]
          have bounds : 0 < index + 2 ∧ 1 < index + 2 := by omega
          simp only [dif_pos bounds]
          cases assignment key <;> simp [eval]

/-- Decision ordering compares positions, so input labels may appear in any order. -/
@[expose] def Diagram.After (diagram : Diagram) (order : List Nat) (key reference : Nat) : Prop :=
  match diagram.node? reference with
  | none => True
  | some node => order.idxOf key < order.idxOf node.key

instance (diagram : Diagram) (order : List Nat) (key reference : Nat) :
    Decidable (diagram.After order key reference) := by
  unfold Diagram.After
  split <;> infer_instance

/-- An ordered diagram has listed labels, earlier children, and distinct branches. -/
@[expose] def Diagram.Valid (diagram : Diagram) (order : List Nat) : Prop :=
  ∀ index : Fin diagram.nodes.size,
    let node := diagram.nodes[index]
    node.key ∈ order ∧ node.low < index.val + 2 ∧ node.high < index.val + 2 ∧
      node.low ≠ node.high ∧ diagram.After order node.key node.low ∧
      diagram.After order node.key node.high

instance (diagram : Diagram) (order : List Nat) : Decidable (diagram.Valid order) :=
  inferInstanceAs (Decidable (∀ _ : Fin _, _))

/-- Extract the checked invariant of a referenced decision node. -/
theorem Diagram.valid_node (diagram : Diagram) {order : List Nat} {reference : Nat} {node : Node}
    (valid : diagram.Valid order) (found : diagram.node? reference = some node) :
    node.key ∈ order ∧ node.low < reference ∧ node.high < reference ∧ node.low ≠ node.high ∧
      diagram.After order node.key node.low ∧ diagram.After order node.key node.high := by
  cases reference with
  | zero => simp [node?] at found
  | succ reference =>
      cases reference with
      | zero => simp [node?] at found
      | succ index =>
          change diagram.nodes[index]? = some node at found
          obtain ⟨bound, equal⟩ := Array.getElem?_eq_some_iff.mp found
          have localValid := valid ⟨index, bound⟩
          change diagram.nodes[index].key ∈ order ∧
            diagram.nodes[index].low < index + 2 ∧ diagram.nodes[index].high < index + 2 ∧
            diagram.nodes[index].low ≠ diagram.nodes[index].high ∧
            diagram.After order diagram.nodes[index].key diagram.nodes[index].low ∧
            diagram.After order diagram.nodes[index].key diagram.nodes[index].high at localValid
          simpa only [equal] using localValid

/-- Unfold the Boolean meaning of a checked decision node. -/
theorem Diagram.eval_node (diagram : Diagram) (assignment : Nat → Bool)
    {reference : Nat} {node : Node} (found : diagram.node? reference = some node)
    (bounds : node.low < reference ∧ node.high < reference) :
    diagram.eval assignment reference =
      if assignment node.key then diagram.eval assignment node.high
      else diagram.eval assignment node.low := by
  cases reference with
  | zero => simp [node?] at found
  | succ reference =>
      cases reference with
      | zero => simp [node?] at found
      | succ index =>
          change diagram.nodes[index]? = some node at found
          rw [eval]
          simp only [found, dif_pos bounds]

end
end Problib.Inference.KnowledgeCompilation
