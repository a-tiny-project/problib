module

public import Problib.Inference.KnowledgeCompilation.Diagram

namespace Problib.Inference.KnowledgeCompilation
public section

/-- A claimed Boolean if-then-else identity between diagram references. -/
structure Statement where
  condition : Nat
  whenTrue : Nat
  whenFalse : Nat
  result : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Local proof rules contain no assignments or truth tables. -/
inductive Rule where
  | terminal
  | split (key lowClaim highClaim : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- One local ITE identity with its finite reconstruction instruction. -/
structure Claim extends Statement where
  rule : Rule
  deriving DecidableEq, Repr, Inhabited

/-- Restrict the four roots to a decision variable. -/
def Statement.cofactor (statement : Statement) (diagram : Diagram)
    (key : Nat) (branch : Bool) : Statement where
  condition := diagram.cofactor statement.condition key branch
  whenTrue := diagram.cofactor statement.whenTrue key branch
  whenFalse := diagram.cofactor statement.whenFalse key branch
  result := diagram.cofactor statement.result key branch

/-- The semantic obligation quantifies over every possible input assignment. -/
def Statement.Holds (statement : Statement) (diagram : Diagram) : Prop :=
  ∀ assignment : Nat → Bool,
    diagram.eval assignment statement.result =
      if diagram.eval assignment statement.condition then
        diagram.eval assignment statement.whenTrue
      else diagram.eval assignment statement.whenFalse

/-- Local terminal identities and earlier cofactor identities are decidable. -/
@[expose] def Rule.Valid (rule : Rule) (diagram : Diagram) (claims : Array Claim)
    (index : Nat) (statement : Statement) : Prop :=
  match rule with
  | .terminal =>
      (statement.condition = 0 ∧ statement.result = statement.whenFalse) ∨
      (statement.condition = 1 ∧ statement.result = statement.whenTrue) ∨
      (statement.whenTrue = statement.whenFalse ∧ statement.result = statement.whenTrue)
  | .split key lowClaim highClaim =>
      lowClaim < index ∧ highClaim < index ∧
      (claims[lowClaim]?.getD default).toStatement = statement.cofactor diagram key false ∧
      (claims[highClaim]?.getD default).toStatement = statement.cofactor diagram key true

instance (rule : Rule) (diagram : Diagram) (claims : Array Claim)
    (index : Nat) (statement : Statement) :
    Decidable (rule.Valid diagram claims index statement) := by
  cases rule <;> unfold Rule.Valid <;> infer_instance

/-- The accepted local rule reconstructs the claimed identity. -/
theorem Rule.sound (rule : Rule) (diagram : Diagram) (claims : Array Claim)
    (index : Nat) (statement : Statement)
    (previous : ∀ prior, prior < index →
      (claims[prior]?.getD default).toStatement.Holds diagram)
    (accepted : rule.Valid diagram claims index statement) : statement.Holds diagram := by
  cases rule with
  | terminal =>
      rcases accepted with ⟨condition, result⟩ | ⟨condition, result⟩ | ⟨same, result⟩
      · intro assignment
        simp [condition, result, Diagram.eval]
      · intro assignment
        simp [condition, result, Diagram.eval]
      · intro assignment
        simp [same, result]
  | split key lowClaim highClaim =>
      rcases accepted with ⟨lowBefore, highBefore, low, high⟩
      have lowHolds := previous lowClaim lowBefore
      have highHolds := previous highClaim highBefore
      rw [low] at lowHolds
      rw [high] at highHolds
      intro assignment
      have selected : (statement.cofactor diagram key (assignment key)).Holds diagram := by
        cases assignment key
        · exact lowHolds
        · exact highHolds
      have equation := selected assignment
      simpa only [Statement.cofactor, Diagram.eval_cofactor] using equation

/-- An untrusted compilation carries the graph and the local proof DAG. -/
structure Compilation where
  order : List Nat
  diagram : Diagram
  roots : Array Nat
  claims : Array Claim
  steps : Array Nat
  deriving Repr, Inhabited

/-- Output roots are indexed by source operation, independently of diagram nodes. -/
@[expose] def Compilation.rootAt (compilation : Compilation) (index : Nat) : Nat :=
  compilation.roots[index]?.getD 0

/-- The statement needed to compile an ITE operation. -/
@[expose] def Compilation.iteStatement (compilation : Compilation)
    (index condition whenTrue whenFalse : Nat) : Statement where
  condition := compilation.rootAt condition
  whenTrue := compilation.rootAt whenTrue
  whenFalse := compilation.rootAt whenFalse
  result := compilation.rootAt index

/-- A source operation selects either a canonical root or a checked local claim.
The step index is read only for an ITE operation; every other entry is padding. -/
@[expose] def Compilation.Matches (compilation : Compilation) (index : Nat) : Operation → Prop
  | .falsity => compilation.rootAt index = 0
  | .truth => compilation.rootAt index = 1
  | .variable key => compilation.diagram.node? (compilation.rootAt index) =
      some ⟨key, 0, 1⟩
  | .ite condition whenTrue whenFalse =>
      let step := compilation.steps[index]?.getD 0
      step < compilation.claims.size ∧
        (compilation.claims[step]?.getD default).toStatement =
          compilation.iteStatement index condition whenTrue whenFalse

instance (compilation : Compilation) (index : Nat) (operation : Operation) :
    Decidable (compilation.Matches index operation) := by
  cases operation <;> unfold Compilation.Matches <;> infer_instance

/-- The finite checker validates both graph structure and source linkage. -/
@[expose] def Compilation.Valid (compilation : Compilation) (source : Circuit) : Prop :=
  source.Valid ∧ compilation.order.isPerm (List.range source.variables) = true ∧
    compilation.diagram.Valid compilation.order ∧
    compilation.roots.size = source.operations.size ∧
    compilation.steps.size = source.operations.size ∧
    (∀ index : Fin compilation.roots.size,
      compilation.roots[index] < compilation.diagram.nodes.size + 2) ∧
    (∀ index : Fin compilation.claims.size,
      let claim := compilation.claims[index]
      claim.rule.Valid compilation.diagram compilation.claims index claim.toStatement) ∧
    (∀ index : Fin source.operations.size,
      compilation.Matches index source.operations[index])

instance (compilation : Compilation) (source : Circuit) :
    Decidable (compilation.Valid source) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Kernel reduction of this checker establishes source equivalence without enumeration. -/
@[expose] def checkCompilation (source : Circuit) (compilation : Compilation) : Bool :=
  decide (compilation.Valid source)

theorem checkCompilation_valid {source : Circuit} {compilation : Compilation}
    (accepted : checkCompilation source compilation = true) : compilation.Valid source :=
  of_decide_eq_true accepted

/-- Every mapped source root is an in-bounds diagram reference. -/
theorem Compilation.rootAt_bound {source : Circuit} (compilation : Compilation)
    (valid : compilation.Valid source) (index : Nat) (bound : index < source.operations.size) :
    compilation.rootAt index < compilation.diagram.nodes.size + 2 := by
  have mapped : index < compilation.roots.size := by
    rw [valid.2.2.2.1]
    exact bound
  have rootBound := valid.2.2.2.2.2.1 ⟨index, mapped⟩
  change compilation.roots[index] < compilation.diagram.nodes.size + 2 at rootBound
  simpa only [rootAt, Array.getElem?_eq_getElem mapped, Option.getD_some] using rootBound

/-- Earlier-claim induction reconstructs every accepted certificate statement. -/
theorem Compilation.claims_sound {source : Circuit} (compilation : Compilation)
    (valid : compilation.Valid source) (index : Nat) (bound : index < compilation.claims.size) :
    (compilation.claims[index]?.getD default).toStatement.Holds compilation.diagram := by
  induction index using Nat.strongRecOn with
  | ind index induction =>
      have localRule := valid.2.2.2.2.2.2.1 ⟨index, bound⟩
      change compilation.claims[index].rule.Valid compilation.diagram compilation.claims index
        compilation.claims[index].toStatement at localRule
      have found : compilation.claims[index]?.getD default = compilation.claims[index] := by
        simp [bound]
      rw [← found] at localRule
      apply Rule.sound _ _ _ index _ (fun prior before => induction prior before (by omega))
      exact localRule

/-- Every linked operation root denotes its source operation for every assignment. -/
theorem Compilation.node_sound {source : Circuit} (compilation : Compilation)
    (valid : compilation.Valid source) (assignment : Nat → Bool)
    (index : Nat) (bound : index < source.operations.size) :
    compilation.diagram.eval assignment (compilation.rootAt index) =
      source.evalAt assignment index := by
  induction index using Nat.strongRecOn with
  | ind index induction =>
      have operationValid := valid.1.2 ⟨index, bound⟩
      have linked := valid.2.2.2.2.2.2.2 ⟨index, bound⟩
      change source.operations[index].Valid source.variables index at operationValid
      change compilation.Matches index source.operations[index] at linked
      rw [Circuit.evalAt]
      simp only [Array.getElem?_eq_getElem bound]
      cases operation : source.operations[index] with
      | falsity =>
          rw [operation] at linked
          exact (congrArg (compilation.diagram.eval assignment) linked).trans (by rw [Diagram.eval])
      | truth =>
          rw [operation] at linked
          exact (congrArg (compilation.diagram.eval assignment) linked).trans (by rw [Diagram.eval])
      | «variable» key =>
          rw [operation] at linked
          exact compilation.diagram.eval_variable assignment _ key linked
      | ite condition whenTrue whenFalse =>
          rw [operation] at operationValid linked
          rcases operationValid with ⟨conditionBefore, trueBefore, falseBefore⟩
          rcases linked with ⟨stepBound, statement⟩
          have holds := compilation.claims_sound valid _ stepBound
          rw [statement] at holds
          have equation := holds assignment
          simp only [Compilation.iteStatement] at equation
          rw [induction condition conditionBefore (by omega),
            induction whenTrue trueBefore (by omega),
            induction whenFalse falseBefore (by omega)] at equation
          have bounds : condition < index ∧ whenTrue < index ∧ whenFalse < index :=
            ⟨conditionBefore, trueBefore, falseBefore⟩
          simpa only [dif_pos bounds] using equation

/-- An accepted compilation preserves the source result for every assignment. -/
theorem checkCompilation_sound {source : Circuit} {compilation : Compilation}
    (accepted : checkCompilation source compilation = true) (assignment : Nat → Bool) :
    compilation.diagram.eval assignment (compilation.rootAt source.root) =
      source.eval assignment := by
  have valid := checkCompilation_valid accepted
  exact compilation.node_sound valid assignment source.root valid.1.1

end
end Problib.Inference.KnowledgeCompilation
