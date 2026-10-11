module

public import Problib.Tree
public import Problib.Measure.Pi
public import Problib.Measure.Space.Sigma
public import Problib.Measure.Space.Sum

set_option autoImplicit false

/-!
# The measurable space of finite trees

A tree is observed at each path of child indices, seeing either nothing or a
label with its field. The measurable space of trees is the coarsest one under
which every observation is measurable. Roll and unroll are measurable and
inverse, and a fold with a measurable algebra is measurable jointly in the tree
and in the parameters the algebra shares. Labels alone determine a tree's shape,
so shapes partition trees countably, and a fold is measured shape by shape.
-/

namespace Problib.Measure

public section

universe v w x y

variable {signature : Signature} {Field : Fin signature.count → Type v}

namespace Space

/-- What a tree shows at one path: nothing, or a label with its field. -/
@[expose, reducible] def treeObservation (fields : ∀ label, Space (Field label)) :
    Space (Sum Unit (Σ label, Field label)) :=
  sum (discrete Unit) (sigma fields)

/-- Finite trees, measured by what they show at every path. -/
@[expose] def tree (fields : ∀ label, Space (Field label)) : Space (Tree signature Field) :=
  comap (fun tree path => Tree.observe path tree) (pi fun _ : List Nat => treeObservation fields)

/-- One layer of the signature functor over a space of children. -/
@[expose, reducible] def treeLayer (fields : ∀ label, Space (Field label)) {α : Type w}
    (children : Space α) : Space (Tree.Layer signature Field α) :=
  sigma fun label => product (fields label) (pi fun _ : Fin (signature.arity label) => children)

end Space

namespace TreeSpace

theorem observe_measurable (fields : ∀ label, Space (Field label)) (path : List Nat) :
    MeasurableMap (Space.tree fields) (Space.treeObservation fields) (Tree.observe path) :=
  MeasurableMap.comp (Space.coordinate_measurable (fun _ : List Nat => Space.treeObservation fields) path)
    (Space.comap_map (fun tree path => Tree.observe path tree) _)

/-- A map into trees is measurable when each of its path observations is. -/
theorem measurable {α : Type w} {source : Space α} {fields : ∀ label, Space (Field label)}
    {function : α → Tree signature Field}
    (observations : ∀ path, MeasurableMap source (Space.treeObservation fields)
      (fun input => Tree.observe path (function input))) :
    MeasurableMap source (Space.tree fields) function := by
  intro region measurable
  obtain ⟨target, targetMeasurable, rfl⟩ := (Space.comap_measurable_iff _ _ region).mp measurable
  exact Space.pi_measurable observations targetMeasurable

theorem observedLabel_measurable (fields : ∀ label, Space (Field label)) :
    MeasurableMap (Space.treeObservation fields) (Space.discrete (Option (Fin signature.count)))
      Tree.observedLabel :=
  fun {region} _ => ⟨trivial, fun label =>
    MeasurableMap.constant (fields label) (Space.discrete _) (some label) (set := region) trivial⟩

/-- The observations whose labels follow one shape are measurable. -/
theorem follows_measurable (fields : ∀ label, Space (Field label)) (form : Tree.Shape signature) :
    (Space.pi fun _ : List Nat => Space.treeObservation fields).Measurable fun observation =>
      ∀ path, Tree.observedLabel (observation path) = Tree.observedLabel (Tree.observe path form) := by
  have differs := Space.i_union_of_nat_injection _ Countable.Pair.encodeList
    Countable.Pair.encodeList_injective _ fun path =>
      MeasurableMap.comp (observedLabel_measurable fields)
        (Space.coordinate_measurable (fun _ : List Nat => Space.treeObservation fields) path)
        (Space.discrete_measurable fun label => ¬label = Tree.observedLabel (Tree.observe path form))
  have equal : (fun observation : List Nat → Sum Unit (Σ label, Field label) =>
      ∀ path, Tree.observedLabel (observation path) = Tree.observedLabel (Tree.observe path form)) =
      Set.complement (fun observation => ∃ path,
        ¬Tree.observedLabel (observation path) = Tree.observedLabel (Tree.observe path form)) := by
    funext observation
    simp [Set.complement]
  rw [equal]
  exact Space.complement _ differs

theorem shape_measurable (fields : ∀ label, Space (Field label)) :
    MeasurableMap (Space.tree fields) (Space.discrete (Tree.Shape signature)) Tree.shape := by
  intro region _
  have pieces : ∀ form, (Space.tree fields).Measurable
      fun tree : Tree signature Field => region form ∧ Tree.shape tree = form := by
    intro form
    by_cases member : region form
    · have equal : (fun tree : Tree signature Field => region form ∧ Tree.shape tree = form) =
          Set.preimage (fun tree path => Tree.observe path tree) fun observation =>
            ∀ path, Tree.observedLabel (observation path) = Tree.observedLabel (Tree.observe path form) := by
        funext tree
        simp [Set.preimage, member, Tree.shape_eq_iff]
      rw [equal]
      exact Space.comap_map _ _ (follows_measurable fields form)
    · have equal : (fun tree : Tree signature Field => region form ∧ Tree.shape tree = form) =
          Set.empty :=
        funext fun _ => propext ⟨fun inside => member inside.1, False.elim⟩
      rw [equal]
      exact Space.empty _
  have equal : Set.preimage (Tree.shape (Field := Field)) region =
      fun tree => ∃ form, region form ∧ Tree.shape tree = form :=
    funext fun tree => propext ⟨fun inside => ⟨_, inside, rfl⟩, fun ⟨_, inside, same⟩ => by subst same; exact inside⟩
  rw [equal]
  exact Space.i_union_of_nat_injection _ (Tree.code fun _ _ => 0)
    (Tree.code_injective fun _ _ _ _ => rfl) _ pieces

theorem rank_measurable (fields : ∀ label, Space (Field label)) :
    MeasurableMap (Space.tree fields) (Space.discrete Nat) Tree.rank :=
  MeasurableMap.comp (MeasurableMap.from_discrete _ (Tree.code fun _ _ => 0)) (shape_measurable fields)

theorem label_measurable (fields : ∀ label, Space (Field label)) :
    MeasurableMap (Space.tree fields) (Space.discrete (Fin signature.count))
      (fun tree => (Tree.unroll tree).1) := by
  intro region _
  have equal : Set.preimage (fun tree : Tree signature Field => (Tree.unroll tree).1) region =
      Set.preimage (fun tree : Tree signature Field => Tree.observedLabel (Tree.observe [] tree))
        (fun label => ∃ found, label = some found ∧ region found) := by
    funext tree
    cases tree
    simp [Set.preimage, Tree.unroll, Tree.observe, Tree.observedLabel]
  rw [equal]
  exact MeasurableMap.comp (observedLabel_measurable fields) (observe_measurable fields []) trivial

theorem root_measurable (fields : ∀ label, Space (Field label)) :
    MeasurableMap (Space.tree fields) (Space.sigma fields)
      (fun tree => (⟨(Tree.unroll tree).1, (Tree.unroll tree).2.1⟩ : Σ label, Field label)) := by
  intro region measurable
  have equal : Set.preimage (fun tree : Tree signature Field =>
      (⟨(Tree.unroll tree).1, (Tree.unroll tree).2.1⟩ : Σ label, Field label)) region =
      Set.preimage (Tree.observe []) (Sum.elim (fun _ => False) region) := by
    funext tree
    cases tree
    rfl
  rw [equal]
  exact observe_measurable fields [] ⟨trivial, measurable⟩

/-- The child at one index, or a default when the root has fewer children. -/
@[expose] def childAt (index : Nat) (default : Tree signature Field) :
    Tree signature Field → Tree signature Field
  | .node label _ children =>
      if bound : index < signature.arity label then children ⟨index, bound⟩ else default

theorem childAt_measurable (fields : ∀ label, Space (Field label)) (index : Nat)
    (default : Tree signature Field) :
    MeasurableMap (Space.tree fields) (Space.tree fields) (childAt index default) := by
  apply measurable
  intro path
  have equal : (fun tree => Tree.observe path (childAt index default tree)) = fun tree =>
      (fun choice : Nat => if choice = 0 then Tree.observe (index :: path) tree
        else Tree.observe path default)
      ((fun label => if index < signature.arity label then 0 else 1) (Tree.unroll tree).1) := by
    funext tree
    obtain ⟨label, field, children⟩ := tree
    by_cases bound : index < signature.arity label <;> simp [childAt, Tree.observe, Tree.unroll, bound]
  rw [equal]
  have branches : ∀ choice : Nat, MeasurableMap (Space.tree fields) (Space.treeObservation fields)
      fun tree => if choice = 0 then Tree.observe (index :: path) tree else Tree.observe path default := by
    intro choice
    by_cases zero : choice = 0
    · simp only [zero, ↓reduceIte]
      exact observe_measurable fields (index :: path)
    · simp only [zero, ↓reduceIte]
      exact MeasurableMap.constant (Space.tree fields) (Space.treeObservation fields) _
  intro region measurable
  exact MeasurableMap.countable_piecewise
    (fun choice => label_measurable fields
      (set := fun label => (if index < signature.arity label then 0 else 1) = choice) trivial)
    branches measurable

theorem roll_measurable (fields : ∀ label, Space (Field label)) :
    MeasurableMap (Space.treeLayer fields (Space.tree fields)) (Space.tree fields) Tree.roll := by
  apply measurable
  intro path
  apply MeasurableMap.from_sigma_iff.mpr
  intro label
  cases path with
  | nil =>
      exact MeasurableMap.comp (MeasurableMap.inr _ _)
        (MeasurableMap.comp (MeasurableMap.sigma_mk fields label) (Space.first_measurable _ _))
  | cons index path =>
      by_cases bound : index < signature.arity label
      · simp only [Tree.roll, Tree.observe, bound, dite_true]
        exact MeasurableMap.comp (observe_measurable fields path)
          (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin (signature.arity label) =>
            Space.tree fields) (⟨index, bound⟩ : Fin (signature.arity label)))
            (Space.second_measurable (fields label) _))
      · simp only [Tree.roll, Tree.observe, bound, dite_false]
        exact MeasurableMap.constant _ _ _

theorem unroll_measurable (fields : ∀ label, Space (Field label)) :
    MeasurableMap (Space.tree fields) (Space.treeLayer fields (Space.tree fields)) Tree.unroll := by
  apply MeasurableMap.into_sigma_of_slices Fin.val (fun _ _ => Fin.ext) (label_measurable fields)
  intro label default
  refine ⟨fun tree => (sigmaSlice label default.1
      (⟨(Tree.unroll tree).1, (Tree.unroll tree).2.1⟩ : Σ label, Field label),
    fun index => childAt index.val (default.2 index) tree), ?_, ?_⟩
  · exact Space.pair_measurable
      (MeasurableMap.comp (MeasurableMap.sigma_slice fields label default.1) (root_measurable fields))
      (Space.pi_measurable fun index => childAt_measurable fields index.val (default.2 index))
  · rintro ⟨other, field, children⟩ same
    change other = label at same
    subst same
    simp [sigmaSlice, childAt, Tree.unroll]

/-- The functor's action on a measurable map that shares a parameter with the
layer. -/
theorem layer_map_measurable (fields : ∀ label, Space (Field label)) {α : Type w} {β : Type x}
    {γ : Type y} {children : Space α} {images : Space β} {parameter : Space γ}
    {function : α × γ → β}
    (functionMeasurable : MeasurableMap (Space.product children parameter) images function) :
    MeasurableMap (Space.product (Space.treeLayer fields children) parameter)
      (Space.treeLayer fields images)
      (fun input => input.1.map fun child => function (child, input.2)) := by
  have fiberwise : MeasurableMap
      (Space.sigma fun label => Space.product
        (Space.product (fields label) (Space.pi fun _ : Fin (signature.arity label) => children)) parameter)
      (Space.treeLayer fields images)
      (fun input => (⟨input.1, input.2.1.1, fun index => function (input.2.1.2 index, input.2.2)⟩ :
        Tree.Layer signature Field β)) := by
    apply MeasurableMap.from_sigma_iff.mpr
    intro label
    show MeasurableMap (Space.product
        (Space.product (fields label) (Space.pi fun _ : Fin (signature.arity label) => children)) parameter)
      (Space.treeLayer fields images)
      (fun input => (⟨label, input.1.1, fun index => function (input.1.2 index, input.2)⟩ :
        Tree.Layer signature Field β))
    exact MeasurableMap.comp (MeasurableMap.sigma_mk _ label) (Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
      (Space.pi_measurable fun index => MeasurableMap.comp functionMeasurable (Space.pair_measurable
        (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin (signature.arity label) => children) index)
          (MeasurableMap.comp (Space.second_measurable (fields label) (Space.pi fun _ => children))
            (Space.first_measurable (Space.product (fields label) (Space.pi fun _ => children)) parameter)))
        (Space.second_measurable (Space.product (fields label) (Space.pi fun _ => children)) parameter))))
  intro region measurable
  exact MeasurableMap.sigma_distribute Fin.val (fun _ _ => Fin.ext) (fiberwise measurable)

/-- A fold cut off after `fuel` levels, with `point` below the cut. -/
@[expose] def foldUpTo {β : Type w} {γ : Type x} (point : β)
    (algebra : Tree.Layer signature Field β × γ → β) :
    Nat → Tree signature Field × γ → β
  | 0, _ => point
  | fuel + 1, input =>
      algebra ((Tree.unroll input.1).map fun child => foldUpTo point algebra fuel (child, input.2), input.2)

theorem foldUpTo_eq {β : Type w} {γ : Type x} (point : β)
    (algebra : Tree.Layer signature Field β × γ → β) (tree : Tree signature Field) :
    ∀ fuel captured, Tree.rank tree < fuel →
      foldUpTo point algebra fuel (tree, captured) = Tree.fold (fun layer => algebra (layer, captured)) tree := by
  induction tree with
  | node label field children induction =>
      intro fuel captured below
      cases fuel with
      | zero => exact absurd below (Nat.not_lt_zero _)
      | succ fuel =>
          have same : (fun index => foldUpTo point algebra fuel (children index, captured)) =
              fun index => Tree.fold (fun layer => algebra (layer, captured)) (children index) :=
            funext fun index => induction index fuel captured (Nat.lt_of_lt_of_le
              (Tree.rank_child_lt label field children index) (Nat.le_of_lt_succ below))
          show algebra (⟨label, field, fun index => foldUpTo point algebra fuel (children index, captured)⟩,
            captured) = _
          rw [same]
          rfl

/-- Folding is jointly measurable in the tree and in the parameters its
algebra shares. Rank selects how many levels a measurable cut-off fold needs. -/
theorem fold_measurable (fields : ∀ label, Space (Field label)) {β : Type w} {γ : Type x}
    {result : Space β} {parameter : Space γ} {algebra : Tree.Layer signature Field β × γ → β}
    (algebraMeasurable : MeasurableMap (Space.product (Space.treeLayer fields result) parameter)
      result algebra) :
    MeasurableMap (Space.product (Space.tree fields) parameter) result
      (fun input => Tree.fold (fun layer => algebra (layer, input.2)) input.1) := by
  by_cases inhabited : Nonempty β
  · obtain ⟨point⟩ := inhabited
    have cut : ∀ fuel, MeasurableMap (Space.product (Space.tree fields) parameter) result
        (foldUpTo point algebra fuel) := by
      intro fuel
      induction fuel with
      | zero => exact MeasurableMap.constant _ _ point
      | succ fuel induction =>
          exact MeasurableMap.comp algebraMeasurable (Space.pair_measurable
            (MeasurableMap.comp (layer_map_measurable fields induction)
              (Space.product_map (unroll_measurable fields) (MeasurableMap.identity parameter)))
            (Space.second_measurable _ _))
    have equal : (fun input : Tree signature Field × γ => foldUpTo point algebra (Tree.rank input.1 + 1) input) =
        fun input => Tree.fold (fun layer => algebra (layer, input.2)) input.1 :=
      funext fun input => foldUpTo_eq point algebra input.1 _ input.2 (Nat.lt_succ_self _)
    rw [← equal]
    exact MeasurableMap.countable_piecewise
      (partition := fun input => Tree.rank input.1)
      (branches := fun rank => foldUpTo point algebra (rank + 1))
      (fun rank => MeasurableMap.comp (rank_measurable fields) (Space.first_measurable _ _)
        (Space.discrete_measurable fun found => found = rank))
      (fun rank => cut (rank + 1))
  · intro _
    have equal : ∀ region, Set.preimage (fun input : Tree signature Field × γ =>
        Tree.fold (fun layer => algebra (layer, input.2)) input.1) region = Set.empty := fun _ =>
      funext fun input => absurd ⟨Tree.fold (fun layer => algebra (layer, input.2)) input.1⟩ inhabited
    rw [equal]
    exact Space.empty _

end TreeSpace

end

end Problib.Measure
