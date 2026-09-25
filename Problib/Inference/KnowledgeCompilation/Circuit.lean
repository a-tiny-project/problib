module

public import Std

namespace Problib.Inference.KnowledgeCompilation
public section

/-- Boolean source operations refer only to earlier operation indices. -/
inductive Operation where
  | falsity
  | truth
  | variable (index : Nat)
  | ite (condition whenTrue whenFalse : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A finite Boolean source circuit with an explicit output operation. -/
structure Circuit where
  variables : Nat
  operations : Array Operation
  root : Nat
  deriving Repr, Inhabited

/-- The local source invariant rejects cycles and unbound variables. -/
@[expose] def Operation.Valid (variables index : Nat) : Operation → Prop
  | .falsity | .truth => True
  | .variable key => key < variables
  | .ite condition whenTrue whenFalse =>
      condition < index ∧ whenTrue < index ∧ whenFalse < index

instance (variables index : Nat) (operation : Operation) :
    Decidable (operation.Valid variables index) := by
  cases operation <;> unfold Operation.Valid <;> infer_instance

/-- A circuit is closed and its operation graph is acyclic. -/
@[expose] def Circuit.Valid (source : Circuit) : Prop :=
  source.root < source.operations.size ∧
    ∀ index : Fin source.operations.size,
      source.operations[index].Valid source.variables index

instance (source : Circuit) : Decidable source.Valid :=
  inferInstanceAs (Decidable (_ ∧ ∀ _ : Fin _, _))

/-- Total interpretation rejects cyclic edges before recursive evaluation. -/
@[expose] def Circuit.evalAt (source : Circuit) (assignment : Nat → Bool) (index : Nat) : Bool :=
  match source.operations[index]? with
  | none => false
  | some .falsity => false
  | some .truth => true
  | some (.variable key) => assignment key
  | some (.ite condition whenTrue whenFalse) =>
      if _bound : condition < index ∧ whenTrue < index ∧ whenFalse < index then
        if source.evalAt assignment condition then source.evalAt assignment whenTrue
        else source.evalAt assignment whenFalse
      else false
termination_by index

/-- Evaluate the designated output of a source circuit. -/
@[expose] def Circuit.eval (source : Circuit) (assignment : Nat → Bool) : Bool :=
  source.evalAt assignment source.root

end
end Problib.Inference.KnowledgeCompilation
