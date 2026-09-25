module

public import Problib.Inference.KnowledgeCompilation.Certificate
public import Problib.Algebra

namespace Problib.Inference.KnowledgeCompilation
public section

open Problib.Algebra

/-- The false and true weights of each Boolean input. -/
abbrev Weights (R : Type) := Nat → R × R

/-- Replace one Boolean input without changing the others. -/
@[expose] def assign (assignment : Nat → Bool) (key : Nat) (value : Bool) : Nat → Bool :=
  fun input => if input = key then value else assignment input

/-- The finite semantic count over an explicit sequence of inputs. -/
@[expose] def orderedSum {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) :
    List Nat → (Nat → Bool) → ((Nat → Bool) → R) → R
  | [], assignment, payoff => payoff assignment
  | label :: rest, assignment, payoff =>
      laws.additive.add
        (laws.multiplicative.mul (weights label).1
          (orderedSum laws weights rest (assign assignment label false) payoff))
        (laws.multiplicative.mul (weights label).2
          (orderedSum laws weights rest (assign assignment label true) payoff))

/-- Assignments to different inputs commute. -/
theorem assign_commute (assignment : Nat → Bool) {left right : Nat}
    (different : left ≠ right) (leftValue rightValue : Bool) :
    assign (assign assignment left leftValue) right rightValue =
      assign (assign assignment right rightValue) left leftValue := by
  funext input
  simp only [assign]
  by_cases leftInput : input = left <;> by_cases rightInput : input = right <;>
    simp_all

theorem semiring_swap {R : Type} (laws : CommutativeSemiringLaws R)
    (a₀ a₁ b₀ b₁ x₀₀ x₀₁ x₁₀ x₁₁ : R) :
    laws.additive.add
      (laws.multiplicative.mul a₀
        (laws.additive.add (laws.multiplicative.mul b₀ x₀₀)
          (laws.multiplicative.mul b₁ x₀₁)))
      (laws.multiplicative.mul a₁
        (laws.additive.add (laws.multiplicative.mul b₀ x₁₀)
          (laws.multiplicative.mul b₁ x₁₁))) =
    laws.additive.add
      (laws.multiplicative.mul b₀
        (laws.additive.add (laws.multiplicative.mul a₀ x₀₀)
          (laws.multiplicative.mul a₁ x₁₀)))
      (laws.multiplicative.mul b₁
        (laws.additive.add (laws.multiplicative.mul a₀ x₀₁)
          (laws.multiplicative.mul a₁ x₁₁))) := by
  let add := laws.additive.add
  let mul := laws.multiplicative.mul
  have mulSwap (x y z : R) : mul x (mul y z) = mul y (mul x z) := by
    dsimp [mul]
    rw [← laws.multiplicative.mul_assoc, laws.multiplicative.mul_comm x y,
      laws.multiplicative.mul_assoc]
  have addSwap (x y z w : R) : add (add x y) (add z w) =
      add (add x z) (add y w) := by
    dsimp [add]
    rw [laws.additive.add_assoc, laws.additive.add_left_comm y z w,
      ← laws.additive.add_assoc]
  dsimp [add, mul] at mulSwap addSwap
  rw [laws.mul_add, laws.mul_add, laws.mul_add, laws.mul_add,
    mulSwap b₀ a₀ x₀₀, mulSwap b₀ a₁ x₁₀,
    mulSwap b₁ a₀ x₀₁, mulSwap b₁ a₁ x₁₁]
  exact addSwap _ _ _ _

/-- Adjacent input sums commute, including the case of repeated labels. -/
theorem orderedSum_swap {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (left right : Nat) (rest : List Nat)
    (assignment : Nat → Bool) (payoff : (Nat → Bool) → R) :
    orderedSum laws weights (left :: right :: rest) assignment payoff =
      orderedSum laws weights (right :: left :: rest) assignment payoff := by
  by_cases different : left = right
  · subst right
    rfl
  · simp only [orderedSum]
    rw [assign_commute assignment different false false,
      assign_commute assignment different false true,
      assign_commute assignment different true false,
      assign_commute assignment different true true]
    exact semiring_swap laws _ _ _ _ _ _ _ _

/-- The semantic count is invariant under permutation of the input sequence. -/
theorem orderedSum_perm {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) {first second : List Nat} (permutation : first.Perm second)
    (assignment : Nat → Bool) (payoff : (Nat → Bool) → R) :
    orderedSum laws weights first assignment payoff =
      orderedSum laws weights second assignment payoff := by
  induction permutation generalizing assignment payoff with
  | nil => rfl
  | @cons head first second permutation induction =>
      simp only [orderedSum]
      rw [induction (assign assignment head false) payoff,
        induction (assign assignment head true) payoff]
  | @swap first second rest =>
      exact (orderedSum_swap laws weights first second rest assignment payoff).symm
  | @trans first middle second left right leftIH rightIH =>
      exact Eq.trans (leftIH assignment payoff) (rightIH assignment payoff)

/-- Summing a forced score bit contributes its high weight exactly when selected. -/
theorem orderedSum_indicator {R : Type} (laws : CommutativeSemiringLaws R)
    (key : Nat) (weight : R) (condition : Bool)
    (assignment : Nat → Bool) (payoff : (Nat → Bool) → R) :
    orderedSum laws (fun _ => (laws.multiplicative.one, weight)) [key] assignment
      (fun input => if input key = condition then payoff input else laws.additive.zero) =
      if condition then laws.multiplicative.mul weight (payoff (assign assignment key true))
      else payoff (assign assignment key false) := by
  cases condition with
  | false =>
      simp only [orderedSum]
      simp only [assign, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
      rw [laws.multiplicative.mul_comm weight laws.additive.zero, laws.zero_mul,
        laws.additive.add_zero, laws.multiplicative.one_mul]
  | true =>
      simp only [orderedSum]
      simp only [assign, Bool.false_eq_true, ↓reduceIte]
      rw [laws.multiplicative.mul_comm laws.multiplicative.one laws.additive.zero,
        laws.zero_mul, laws.additive.zero_add]

/-- Fixing a label absent from the sum can be moved into its payoff. -/
theorem orderedSum_assign_outside {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (order : List Nat) (key : Nat) (value : Bool)
    (outside : key ∉ order) (assignment : Nat → Bool)
    (payoff : (Nat → Bool) → R) :
    orderedSum laws weights order (assign assignment key value) payoff =
      orderedSum laws weights order assignment
        (fun input => payoff (assign input key value)) := by
  induction order generalizing assignment with
  | nil => rfl
  | cons label rest induction =>
      have different : key ≠ label := by
        intro equal
        apply outside
        simp [equal]
      have outsideRest : key ∉ rest := by
        intro member
        exact outside (List.mem_cons_of_mem _ member)
      simp only [orderedSum]
      rw [assign_commute assignment different value false,
        assign_commute assignment different value true]
      rw [induction outsideRest (assign assignment label false),
        induction outsideRest (assign assignment label true)]

/-- A sum is independent of its initial assignment when the payoff reads only summed labels. -/
theorem orderedSum_initial_irrel {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (order : List Nat) (nodup : order.Nodup)
    (payoff : (Nat → Bool) → R)
    (depends : ∀ first second : Nat → Bool,
      (∀ key, key ∈ order → first key = second key) → payoff first = payoff second)
    (first second : Nat → Bool) :
    orderedSum laws weights order first payoff =
      orderedSum laws weights order second payoff := by
  induction order generalizing payoff first second with
  | nil =>
      simp only [orderedSum]
      apply depends
      intro key member
      simp at member
  | cons label rest induction =>
      have outside : label ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      simp only [orderedSum]
      have branch (value : Bool) :
          orderedSum laws weights rest (assign first label value) payoff =
            orderedSum laws weights rest (assign second label value) payoff := by
        rw [orderedSum_assign_outside laws weights rest label value outside first payoff,
          orderedSum_assign_outside laws weights rest label value outside second payoff]
        apply induction restNodup
        intro left right agree
        apply depends
        intro key member
        rcases List.mem_cons.mp member with equal | inRest
        · subst key
          simp [assign]
        · have distinct : key ≠ label := by
            intro equal
            subst key
            exact outside inRest
          simp only [assign, if_neg distinct]
          exact agree key inRest
      rw [branch false, branch true]

/-- Pointwise equal payoffs have equal ordered sums. -/
theorem orderedSum_congr {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (order : List Nat) (assignment : Nat → Bool)
    (first second : (Nat → Bool) → R)
    (equal : ∀ input, first input = second input) :
    orderedSum laws weights order assignment first =
      orderedSum laws weights order assignment second := by
  induction order generalizing assignment with
  | nil => exact equal assignment
  | cons key rest induction =>
      simp only [orderedSum]
      rw [induction (assign assignment key false),
        induction (assign assignment key true)]

/-- The position order inherited by a child is transitive. -/
theorem Diagram.after_trans (diagram : Diagram) (order : List Nat)
    {first second reference : Nat} (before : order.idxOf first < order.idxOf second)
    (after : diagram.After order second reference) :
    diagram.After order first reference := by
  unfold Diagram.After at after ⊢
  split <;> simp_all <;> omega

/-- Assigning a label earlier than a node cannot change the node's value. -/
theorem Diagram.eval_assign_earlier (diagram : Diagram) (order : List Nat)
    (valid : diagram.Valid order) (assignment : Nat → Bool)
    (key reference : Nat) (value : Bool)
    (earlier : diagram.After order key reference) :
    diagram.eval (assign assignment key value) reference =
      diagram.eval assignment reference := by
  induction reference using Nat.strongRecOn with
  | ind reference induction =>
      cases reference with
      | zero => simp [Diagram.eval]
      | succ reference =>
          cases reference with
          | zero => simp [Diagram.eval]
          | succ index =>
              simp only [Diagram.eval]
              split
              · rfl
              · rename_i node found
                split
                · rename_i bounds
                  have foundNode : diagram.node? (index + 2) = some node := by
                    simpa only [Diagram.node?] using found
                  have localValid := diagram.valid_node valid foundNode
                  have later : order.idxOf key < order.idxOf node.key := by
                    simpa only [Diagram.After, foundNode] using earlier
                  have different : node.key ≠ key := by
                    intro equal
                    subst key
                    omega
                  have lowAfter := diagram.after_trans order later localValid.2.2.2.2.1
                  have highAfter := diagram.after_trans order later localValid.2.2.2.2.2
                  simp only [assign, if_neg different]
                  rw [induction node.low bounds.1 lowAfter,
                    induction node.high bounds.2 highAfter]
                · rfl

/-- Summing an unused input contributes its two weights as a factor. -/
theorem orderedSum_skip {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (key : Nat) (rest : List Nat)
    (outside : key ∉ rest) (assignment : Nat → Bool)
    (payoff : (Nat → Bool) → R)
    (unused : ∀ input value, payoff (assign input key value) = payoff input) :
    orderedSum laws weights (key :: rest) assignment payoff =
      laws.multiplicative.mul
        (laws.additive.add (weights key).1 (weights key).2)
        (orderedSum laws weights rest assignment payoff) := by
  simp only [orderedSum]
  rw [orderedSum_assign_outside laws weights rest key false outside assignment payoff,
    orderedSum_assign_outside laws weights rest key true outside assignment payoff,
    orderedSum_congr laws weights rest assignment _ _ (fun input => unused input false),
    orderedSum_congr laws weights rest assignment _ _ (fun input => unused input true)]
  exact (Problib.Algebra.CommutativeSemiringLaws.add_mul laws (weights key).1 (weights key).2 _).symm

/-- The sum skips a diagram input that occurs before the referenced node. -/
theorem Diagram.orderedSum_skip (diagram : Diagram) (order : List Nat)
    (valid : diagram.Valid order) {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (payoff : Bool → R)
    (key : Nat) (rest : List Nat) (outside : key ∉ rest)
    (reference : Nat) (earlier : diagram.After order key reference)
    (assignment : Nat → Bool) :
    orderedSum laws weights (key :: rest) assignment
      (fun input => payoff (diagram.eval input reference)) =
      laws.multiplicative.mul
        (laws.additive.add (weights key).1 (weights key).2)
        (orderedSum laws weights rest assignment
          (fun input => payoff (diagram.eval input reference))) := by
  apply Problib.Inference.KnowledgeCompilation.orderedSum_skip laws weights key rest outside assignment
  intro input value
  exact congrArg payoff (diagram.eval_assign_earlier order valid input key reference value earlier)

/-- Summing the root decision separates the false and true children. -/
theorem Diagram.orderedSum_node (diagram : Diagram) (order : List Nat)
    (valid : diagram.Valid order) {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (payoff : Bool → R)
    {reference : Nat} {node : Node}
    (found : diagram.node? reference = some node)
    (bounds : node.low < reference ∧ node.high < reference)
    (rest : List Nat) (outside : node.key ∉ rest)
    (assignment : Nat → Bool) :
    orderedSum laws weights (node.key :: rest) assignment
      (fun input => payoff (diagram.eval input reference)) =
      laws.additive.add
        (laws.multiplicative.mul (weights node.key).1
          (orderedSum laws weights rest assignment
            (fun input => payoff (diagram.eval input node.low))))
        (laws.multiplicative.mul (weights node.key).2
          (orderedSum laws weights rest assignment
            (fun input => payoff (diagram.eval input node.high)))) := by
  have localValid := diagram.valid_node valid found
  have branch (value : Bool) (child : Nat)
      (after : diagram.After order node.key child)
      (selected : (if value then node.high else node.low) = child) :
      orderedSum laws weights rest (assign assignment node.key value)
        (fun input => payoff (diagram.eval input reference)) =
        orderedSum laws weights rest assignment
          (fun input => payoff (diagram.eval input child)) := by
    rw [orderedSum_assign_outside laws weights rest node.key value outside assignment]
    apply orderedSum_congr
    intro input
    rw [diagram.eval_node (assign input node.key value) found bounds]
    simp only [assign, ↓reduceIte]
    cases value with
    | false =>
        simp only [Bool.false_eq_true, ite_false] at selected ⊢
        subst child
        exact congrArg payoff
          (diagram.eval_assign_earlier order valid input node.key node.low false after)
    | true =>
        simp at selected ⊢
        subst child
        exact congrArg payoff
          (diagram.eval_assign_earlier order valid input node.key node.high true after)
  simp only [orderedSum]
  rw [branch false node.low localValid.2.2.2.2.1 rfl,
    branch true node.high localValid.2.2.2.2.2 rfl]

/-- An ordered diagram reads only the labels named by its order. -/
theorem Diagram.eval_congr_order (diagram : Diagram) (order : List Nat)
    (valid : diagram.Valid order) (first second : Nat → Bool)
    (agree : ∀ key, key ∈ order → first key = second key)
    (reference : Nat) :
    diagram.eval first reference = diagram.eval second reference := by
  induction reference using Nat.strongRecOn with
  | ind reference induction =>
      cases reference with
      | zero => simp [Diagram.eval]
      | succ reference =>
          cases reference with
          | zero => simp [Diagram.eval]
          | succ index =>
              simp only [Diagram.eval]
              split
              · rfl
              · rename_i node found
                split
                · rename_i bounds
                  have foundNode : diagram.node? (index + 2) = some node := by
                    simpa only [Diagram.node?] using found
                  have localValid := diagram.valid_node valid foundNode
                  rw [agree node.key localValid.1,
                    induction node.low bounds.1,
                    induction node.high bounds.2]
                · rfl

/-- The product of the total weights of a sequence of skipped inputs. -/
@[expose] def skipFactor {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) : List Nat → R
  | [] => laws.multiplicative.one
  | key :: rest =>
      laws.multiplicative.mul
        (laws.additive.add (weights key).1 (weights key).2)
        (skipFactor laws weights rest)

/-- Every skipped factor vanishes under normalized input weights. -/
theorem skipFactor_eq_one {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (keys : List Nat)
    (normalized : ∀ key, key ∈ keys →
      laws.additive.add (weights key).1 (weights key).2 = laws.multiplicative.one) :
    skipFactor laws weights keys = laws.multiplicative.one := by
  induction keys with
  | nil => rfl
  | cons key rest induction =>
      have head := normalized key (List.mem_cons_self)
      have tail : ∀ item, item ∈ rest →
          laws.additive.add (weights item).1 (weights item).2 =
            laws.multiplicative.one := by
        intro item member
        exact normalized item (List.mem_cons_of_mem _ member)
      simp only [skipFactor, head, induction tail]
      exact laws.multiplicative.mul_one _

/-- A beforeKeys unused by a diagram reference contributes exactly its total factor. -/
theorem Diagram.orderedSum_skip_beforeKeys (diagram : Diagram) (order : List Nat)
    (valid : diagram.Valid order) {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (payoff : Bool → R)
    (beforeKeys suffix : List Nat) (nodup : (beforeKeys ++ suffix).Nodup)
    (reference : Nat)
    (earlier : ∀ key, key ∈ beforeKeys → diagram.After order key reference)
    (assignment : Nat → Bool) :
    orderedSum laws weights (beforeKeys ++ suffix) assignment
      (fun input => payoff (diagram.eval input reference)) =
      laws.multiplicative.mul (skipFactor laws weights beforeKeys)
        (orderedSum laws weights suffix assignment
          (fun input => payoff (diagram.eval input reference))) := by
  induction beforeKeys generalizing assignment with
  | nil =>
      simp only [List.nil_append, skipFactor]
      exact (laws.multiplicative.one_mul _).symm
  | cons key rest induction =>
      have outside : key ∉ rest ++ suffix := (List.nodup_cons.mp nodup).1
      have restNodup : (rest ++ suffix).Nodup := (List.nodup_cons.mp nodup).2
      have keyEarlier := earlier key (List.mem_cons_self)
      have restEarlier : ∀ item, item ∈ rest → diagram.After order item reference := by
        intro item member
        exact earlier item (List.mem_cons_of_mem key member)
      simp only [List.cons_append]
      rw [diagram.orderedSum_skip order valid laws weights payoff key
        (rest ++ suffix) outside reference keyEarlier assignment,
        induction restNodup restEarlier assignment]
      simp only [skipFactor]
      exact (laws.multiplicative.mul_assoc _ _ _).symm

/-- The semantic sum factors labels between two order positions. -/
theorem Diagram.orderedSum_between (diagram : Diagram) (order : List Nat)
    (valid : diagram.Valid order) (nodup : order.Nodup)
    {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (payoff : Bool → R)
    (start stop : Nat) (before : start ≤ stop)
    (reference : Nat)
    (earlier : ∀ key,
      key ∈ (order.drop start).take (stop - start) →
        diagram.After order key reference)
    (assignment : Nat → Bool) :
    orderedSum laws weights (order.drop start) assignment
      (fun input => payoff (diagram.eval input reference)) =
      laws.multiplicative.mul
        (skipFactor laws weights ((order.drop start).take (stop - start)))
        (orderedSum laws weights (order.drop stop) assignment
          (fun input => payoff (diagram.eval input reference))) := by
  have dropEq : (order.drop start).drop (stop - start) = order.drop stop := by
    rw [List.drop_drop, Nat.add_sub_of_le before]
  have split : (order.drop start).take (stop - start) ++ order.drop stop =
      order.drop start := by
    rw [← dropEq, List.take_append_drop]
  have suffixNodup :
      ((order.drop start).take (stop - start) ++ order.drop stop).Nodup := by
    rw [split]
    exact nodup.sublist (List.drop_sublist start order)
  simpa only [split] using
    (diagram.orderedSum_skip_beforeKeys order valid laws weights payoff
      _ _ suffixNodup reference earlier assignment)

/-- The decision position of a nonterminal, or the end position of a terminal. -/
@[expose] def Diagram.position (diagram : Diagram) (order : List Nat)
    (reference : Nat) : Nat :=
  match diagram.node? reference with
  | none => order.length
  | some node => order.idxOf node.key

/-- A checked child starts strictly after its parent decision. -/
theorem Diagram.position_after (diagram : Diagram) (order : List Nat)
    (key : Nat) (member : key ∈ order) (reference : Nat)
    (after : diagram.After order key reference) :
    order.idxOf key < diagram.position order reference := by
  cases found : diagram.node? reference with
  | none =>
      simpa only [Diagram.position, found] using
        (List.idxOf_lt_length_of_mem member)
  | some node =>
      simpa only [Diagram.position, Diagram.After, found] using after

/-- Every reference position lies within the declared order. -/
theorem Diagram.position_le_length (diagram : Diagram) (order : List Nat)
    (reference : Nat) : diagram.position order reference ≤ order.length := by
  unfold Diagram.position
  split
  · exact Nat.le_refl _
  · exact List.idxOf_le_length

/-- Membership in an initial list segment bounds the label's first position. -/
theorem idxOf_lt_of_mem_take (order : List Nat) (position key : Nat)
    (member : key ∈ order.take position) :
    order.idxOf key < position := by
  have first : order.idxOf key = (order.take position).idxOf key := by
    calc
      order.idxOf key = (order.take position ++ order.drop position).idxOf key :=
        congrArg (fun values => values.idxOf key)
          (List.take_append_drop position order).symm
      _ = (order.take position).idxOf key := by
        rw [List.idxOf_append, if_pos member]
  have inside := List.idxOf_lt_length_of_mem member
  have lengthBound := List.length_take_le position order
  rw [first]
  omega

/-- Membership between two positions puts a label before the latter. -/
theorem idxOf_lt_of_mem_between (order : List Nat) (start stop key : Nat)
    (before : start ≤ stop)
    (member : key ∈ (order.drop start).take (stop - start)) :
    order.idxOf key < stop := by
  have inTake : key ∈ order.take stop := by
    have split := List.take_add (l := order) (i := start) (j := stop - start)
    rw [Nat.add_sub_of_le before] at split
    rw [split]
    exact List.mem_append.mpr (Or.inr member)
  exact idxOf_lt_of_mem_take order stop key inTake

/-- A label at an earlier position precedes the referenced decision. -/
theorem Diagram.after_of_position (diagram : Diagram) (order : List Nat)
    (key reference : Nat)
    (before : order.idxOf key < diagram.position order reference) :
    diagram.After order key reference := by
  cases found : diagram.node? reference with
  | none => simp [Diagram.After, found]
  | some node =>
      simpa only [Diagram.After, Diagram.position, found] using before

/-- Dropping to a listed label starts with that label. -/
theorem drop_idxOf_cons (order : List Nat) (key : Nat) (member : key ∈ order) :
    order.drop (order.idxOf key) = key :: order.drop (order.idxOf key + 1) := by
  induction order with
  | nil => simp at member
  | cons head tail induction =>
      by_cases equal : head = key
      · subst head
        simp
      · have tailMember : key ∈ tail := by
          rcases List.mem_cons.mp member with same | inTail
          · exact False.elim (equal same.symm)
          · exact inTail
        simpa only [List.idxOf_cons, cond_eq_ite, beq_iff_eq,
          if_neg equal, List.drop_succ_cons, Nat.add_assoc] using
          induction tailMember

/-- All labels before a reference's position factor out of its sum. -/
theorem Diagram.orderedSum_to_position (diagram : Diagram) (order : List Nat)
    (valid : diagram.Valid order) (nodup : order.Nodup)
    {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (payoff : Bool → R)
    (start reference : Nat)
    (before : start ≤ diagram.position order reference)
    (assignment : Nat → Bool) :
    orderedSum laws weights (order.drop start) assignment
      (fun input => payoff (diagram.eval input reference)) =
      laws.multiplicative.mul
        (skipFactor laws weights
          ((order.drop start).take (diagram.position order reference - start)))
        (orderedSum laws weights (order.drop (diagram.position order reference)) assignment
          (fun input => payoff (diagram.eval input reference))) := by
  apply diagram.orderedSum_between order valid nodup laws weights payoff
    start (diagram.position order reference) before reference
  intro key member
  apply diagram.after_of_position order
  exact idxOf_lt_of_mem_between order start
    (diagram.position order reference) key before member

/-- Multiply totals for labels strictly between a parent and one child. -/
@[expose] def Diagram.edgeFactor {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (weights : Weights R) (parentPosition child : Nat) : R :=
  skipFactor laws weights
    ((order.drop (parentPosition + 1)).take
      (diagram.position order child - (parentPosition + 1)))

/-- Evaluate each shared node once in topological array order. -/
@[expose] def Diagram.countPrefix {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (weights : Weights R) (payoff : Bool → R) : Nat → Array R
  | 0 => #[payoff false, payoff true]
  | count + 1 =>
      let values := diagram.countPrefix laws order weights payoff count
      let value := match diagram.nodes[count]? with
        | none => laws.additive.zero
        | some node =>
            let parentPosition := order.idxOf node.key
            let low := laws.multiplicative.mul
              (diagram.edgeFactor laws order weights parentPosition node.low)
              (values[node.low]?.getD laws.additive.zero)
            let high := laws.multiplicative.mul
              (diagram.edgeFactor laws order weights parentPosition node.high)
              (values[node.high]?.getD laws.additive.zero)
            laws.additive.add
              (laws.multiplicative.mul (weights node.key).1 low)
              (laws.multiplicative.mul (weights node.key).2 high)
      values.push value

/-- Shared-node evaluation includes labels preceding the requested root. -/
@[expose] def Diagram.countAtShared {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (weights : Weights R) (payoff : Bool → R) (reference : Nat) : R :=
  let values := diagram.countPrefix laws order weights payoff diagram.nodes.size
  laws.multiplicative.mul
    (skipFactor laws weights (order.take (diagram.position order reference)))
    (values[reference]?.getD laws.additive.zero)

/-- A prefix carries two terminal values and one value per retained node. -/
theorem Diagram.countPrefix_size {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (weights : Weights R) (payoff : Bool → R) (count : Nat) :
    (diagram.countPrefix laws order weights payoff count).size = count + 2 := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [Diagram.countPrefix, Array.size_push, induction]

/-- Pluck's on-path convention omits factors for skipped inputs. -/
@[expose] def Diagram.omittingPrefix {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (weights : Weights R)
    (payoff : Bool → R) : Nat → Array R
  | 0 => #[payoff false, payoff true]
  | count + 1 =>
      let values := diagram.omittingPrefix laws weights payoff count
      let value := match diagram.nodes[count]? with
        | none => laws.additive.zero
        | some node =>
            laws.additive.add
              (laws.multiplicative.mul (weights node.key).1
                (values[node.low]?.getD laws.additive.zero))
              (laws.multiplicative.mul (weights node.key).2
                (values[node.high]?.getD laws.additive.zero))
      values.push value

/-- Read the on-path count at one diagram reference. -/
@[expose] def Diagram.countOmitting {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (weights : Weights R)
    (payoff : Bool → R) (reference : Nat) : R :=
  (diagram.omittingPrefix laws weights payoff diagram.nodes.size)[reference]?.getD
    laws.additive.zero

/-- Every listed key in a segment inherits normalization from the full order. -/
theorem skipFactor_normalized {R : Type} (laws : CommutativeSemiringLaws R)
    (weights : Weights R) (order keys : List Nat)
    (normalized : ∀ key, key ∈ order →
      laws.additive.add (weights key).1 (weights key).2 = laws.multiplicative.one)
    (subset : keys.Sublist order) :
    skipFactor laws weights keys = laws.multiplicative.one :=
  skipFactor_eq_one laws weights keys
    (fun key member => normalized key (subset.subset member))

/-- Edge omissions disappear when each Boolean input has total weight one. -/
theorem Diagram.edgeFactor_normalized {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (weights : Weights R)
    (normalized : ∀ key, key ∈ order →
      laws.additive.add (weights key).1 (weights key).2 = laws.multiplicative.one)
    (parentPosition child : Nat) :
    diagram.edgeFactor laws order weights parentPosition child =
      laws.multiplicative.one := by
  unfold Diagram.edgeFactor
  apply skipFactor_normalized laws weights order _ normalized
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

/-- The two array passes agree at every prefix under normalization. -/
theorem Diagram.omittingPrefix_eq_countPrefix {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (weights : Weights R) (payoff : Bool → R)
    (normalized : ∀ key, key ∈ order →
      laws.additive.add (weights key).1 (weights key).2 = laws.multiplicative.one)
    (count : Nat) :
    diagram.omittingPrefix laws weights payoff count =
      diagram.countPrefix laws order weights payoff count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [Diagram.omittingPrefix, Diagram.countPrefix, induction]
      split
      · rfl
      · rename_i node found
        rw [diagram.edgeFactor_normalized laws order weights normalized
            (order.idxOf node.key) node.low,
          diagram.edgeFactor_normalized laws order weights normalized
            (order.idxOf node.key) node.high,
          laws.multiplicative.one_mul,
          laws.multiplicative.one_mul]

/-- Each retained value counts the suffix beginning at its own decision. -/
theorem Diagram.countPrefix_correct {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (valid : diagram.Valid order) (nodup : order.Nodup)
    (weights : Weights R) (payoff : Bool → R)
    (count : Nat) (within : count ≤ diagram.nodes.size)
    (reference : Nat) (bound : reference < count + 2) :
    (diagram.countPrefix laws order weights payoff count)[reference]?.getD
        laws.additive.zero =
      orderedSum laws weights (order.drop (diagram.position order reference))
        (fun _ => false) (fun input => payoff (diagram.eval input reference)) := by
  induction count generalizing reference with
  | zero =>
      have terminal : reference = 0 ∨ reference = 1 := by omega
      rcases terminal with terminal | terminal <;> subst reference <;>
        simp [Diagram.countPrefix, Diagram.position, Diagram.node?,
          Diagram.eval, orderedSum]
  | succ count induction =>
      have nodeBound : count < diagram.nodes.size := by omega
      let node := diagram.nodes[count]
      have found : diagram.node? (count + 2) = some node := by
        simp [Diagram.node?, node, nodeBound]
      have localValid := diagram.valid_node valid found
      rw [Diagram.countPrefix]
      simp only [Array.getElem?_push, Diagram.countPrefix_size]
      by_cases last : reference = count + 2
      · subst reference
        simp only [↓reduceIte, Option.getD_some, Array.getElem?_eq_getElem nodeBound]
        let parentPosition := order.idxOf node.key
        have parentAt : diagram.position order (count + 2) = parentPosition := by
          simp [Diagram.position, found, parentPosition]
        have parentMember := localValid.1
        have parentSuffix : order.drop parentPosition =
            node.key :: order.drop (parentPosition + 1) := by
          exact drop_idxOf_cons order node.key parentMember
        have lowBefore : parentPosition + 1 ≤ diagram.position order node.low :=
          Nat.succ_le_of_lt
            (diagram.position_after order node.key parentMember node.low
              localValid.2.2.2.2.1)
        have highBefore : parentPosition + 1 ≤ diagram.position order node.high :=
          Nat.succ_le_of_lt
            (diagram.position_after order node.key parentMember node.high
              localValid.2.2.2.2.2)
        have lowSum := diagram.orderedSum_to_position order valid nodup laws weights payoff
          (parentPosition + 1) node.low lowBefore (fun _ => false)
        have highSum := diagram.orderedSum_to_position order valid nodup laws weights payoff
          (parentPosition + 1) node.high highBefore (fun _ => false)
        change orderedSum laws weights (order.drop (parentPosition + 1))
            (fun _ => false) (fun input => payoff (diagram.eval input node.low)) =
          laws.multiplicative.mul
            (diagram.edgeFactor laws order weights parentPosition node.low)
            (orderedSum laws weights (order.drop (diagram.position order node.low))
              (fun _ => false) (fun input => payoff (diagram.eval input node.low)))
          at lowSum
        change orderedSum laws weights (order.drop (parentPosition + 1))
            (fun _ => false) (fun input => payoff (diagram.eval input node.high)) =
          laws.multiplicative.mul
            (diagram.edgeFactor laws order weights parentPosition node.high)
            (orderedSum laws weights (order.drop (diagram.position order node.high))
              (fun _ => false) (fun input => payoff (diagram.eval input node.high)))
          at highSum
        rw [parentAt, parentSuffix,
          diagram.orderedSum_node order valid laws weights payoff found
            ⟨localValid.2.1, localValid.2.2.1⟩
            (order.drop (parentPosition + 1))
            (by
              have restNodup : (order.drop parentPosition).Nodup :=
                nodup.sublist (List.drop_sublist parentPosition order)
              rw [parentSuffix] at restNodup
              exact (List.nodup_cons.mp restNodup).1)
            (fun _ => false)]
        rw [lowSum, highSum,
          ← induction (by omega) node.low localValid.2.1,
          ← induction (by omega) node.high localValid.2.2.1]
      · simp only [if_neg last]
        exact induction (by omega) reference (by omega)

/-- Count a diagram semantically, retaining the assignment for inputs outside the order. -/
@[expose] def Diagram.count {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (weights : Weights R) (payoff : Bool → R)
    (assignment : Nat → Bool) (reference : Nat) : R :=
  orderedSum laws weights order assignment
    (fun input => payoff (diagram.eval input reference))

/-- The source-independent exact count evaluates each shared node once. -/
@[expose] def Diagram.countAt {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (weights : Weights R) (payoff : Bool → R) (reference : Nat) : R :=
  diagram.countAtShared laws order weights payoff reference

/-- The shared-node pass equals the semantic count for a valid ordered diagram. -/
theorem Diagram.countAtShared_eq_count {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (valid : diagram.Valid order) (nodup : order.Nodup)
    (weights : Weights R) (payoff : Bool → R)
    (reference : Nat) (bound : reference < diagram.nodes.size + 2) :
    diagram.countAtShared laws order weights payoff reference =
      diagram.count laws order weights payoff (fun _ => false) reference := by
  have suffix := diagram.countPrefix_correct laws order valid nodup weights payoff
    diagram.nodes.size (Nat.le_refl _) reference bound
  have factor := diagram.orderedSum_to_position order valid nodup laws weights payoff
    0 reference (Nat.zero_le _) (fun _ => false)
  simp only [List.drop_zero] at factor
  unfold Diagram.countAtShared Diagram.count
  dsimp
  rw [suffix]
  exact factor.symm

/-- The shared count agrees with the semantic ordered sum. -/
theorem Diagram.countAt_eq_count {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (valid : diagram.Valid order) (nodup : order.Nodup)
    (weights : Weights R) (payoff : Bool → R)
    (reference : Nat) (bound : reference < diagram.nodes.size + 2) :
    diagram.countAt laws order weights payoff reference =
      diagram.count laws order weights payoff (fun _ => false) reference :=
  diagram.countAtShared_eq_count laws order valid nodup weights payoff reference bound

/-- Omitting skip factors is exact for normalized input weights. -/
theorem countOmitting_eq {R : Type} (diagram : Diagram)
    (laws : CommutativeSemiringLaws R) (order : List Nat)
    (weights : Weights R) (payoff : Bool → R) (reference : Nat)
    (normalized : ∀ key, key ∈ order →
      laws.additive.add (weights key).1 (weights key).2 = laws.multiplicative.one) :
    diagram.countOmitting laws weights payoff reference =
      diagram.countAt laws order weights payoff reference := by
  unfold Diagram.countOmitting Diagram.countAt Diagram.countAtShared
  rw [diagram.omittingPrefix_eq_countPrefix laws order weights payoff normalized
    diagram.nodes.size]
  have root : skipFactor laws weights
      (order.take (diagram.position order reference)) = laws.multiplicative.one :=
    skipFactor_normalized laws weights order _ normalized (List.take_sublist _ _)
  rw [root, laws.multiplicative.one_mul]

/-- A skipped input with total weight different from one changes the count. -/
theorem countOmitting_necessary_of_nonidempotent {R : Type}
    (laws : CommutativeSemiringLaws R)
    (nonidempotent : laws.additive.add laws.multiplicative.one
      laws.multiplicative.one ≠ laws.multiplicative.one) :
    ∃ (diagram : Diagram) (order : List Nat) (weights : Weights R),
      diagram.Valid order ∧
      diagram.countOmitting laws weights (fun _ => laws.multiplicative.one) 1 ≠
        diagram.countAt laws order weights (fun _ => laws.multiplicative.one) 1 := by
  refine ⟨⟨#[]⟩, [0], (fun _ => (laws.multiplicative.one, laws.multiplicative.one)), ?_, ?_⟩
  · intro index
    exact Fin.elim0 index
  · simpa [Diagram.countOmitting, Diagram.omittingPrefix, Diagram.countAt,
      Diagram.countAtShared, Diagram.countPrefix, Diagram.position, Diagram.node?,
      skipFactor, laws.multiplicative.mul_one] using nonidempotent.symm

/-- Every initial assignment gives the same weighted count for an ordered diagram. -/
theorem weighted_count_sound {R : Type} (laws : CommutativeSemiringLaws R)
    (diagram : Diagram) (order : List Nat) (valid : diagram.Valid order)
    (nodup : order.Nodup) (weights : Weights R) (payoff : Bool → R)
    (reference : Nat) (bound : reference < diagram.nodes.size + 2)
    (assignment : Nat → Bool) :
    diagram.countAt laws order weights payoff reference =
      orderedSum laws weights order assignment
        (fun input => payoff (diagram.eval input reference)) := by
  rw [diagram.countAt_eq_count laws order valid nodup weights payoff reference bound]
  unfold Diagram.count
  apply orderedSum_initial_irrel laws weights order nodup
  intro first second agree
  exact congrArg payoff (diagram.eval_congr_order order valid first second agree reference)

end
end Problib.Inference.KnowledgeCompilation
