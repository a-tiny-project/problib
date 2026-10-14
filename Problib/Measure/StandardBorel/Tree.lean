module

public import Problib.Measure.Space.Tree
public import Problib.Measure.Configuration.StandardBorel

set_option autoImplicit false

/-!
# Standard-Borel trees

Finite trees over standard-Borel fields are standard Borel. A tree embeds into
its observations at every path, a countable product of standard-Borel spaces.
The image is the observations whose labels follow some shape: a countable union
over shapes of countable intersections over paths.
-/

namespace Problib.Measure

public section

universe v

variable {signature : Signature} {Field : Fin signature.count → Type v}

namespace TreeSpace

/-- A tree is its observations at every path. -/
@[expose] def embedding (fields : ∀ label, Space (Field label)) :
    MeasurableEmbedding (Space.tree fields) (Space.pi fun _ : List Nat => Space.treeObservation fields) where
  function := fun tree path => Tree.observe path tree
  injective := fun _ _ equal => Tree.observe_injective (congrFun equal)
  measurable := Space.comap_map _ _
  image_measurable := by
    intro region measurable
    obtain ⟨target, targetMeasurable, rfl⟩ := (Space.comap_measurable_iff _ _ region).mp measurable
    have equal : Set.image (fun tree path => Tree.observe path tree)
        (Set.preimage (fun tree path => Tree.observe path tree) target) =
        Set.inter target fun observation => ∃ form : Tree.Shape signature,
          ∀ path, Tree.observedLabel (observation path) = Tree.observedLabel (Tree.observe path form) := by
      funext observation
      apply propext
      constructor
      · rintro ⟨tree, member, rfl⟩
        exact ⟨member, Tree.shape tree, fun path => (Tree.observedLabel_shape path tree).symm⟩
      · rintro ⟨member, form, agree⟩
        obtain ⟨tree, observed⟩ := Tree.exists_observe form observation agree
        have same : (fun path => Tree.observe path tree) = observation := funext observed
        refine ⟨tree, ?_, same⟩
        show target fun path => Tree.observe path tree
        rw [same]
        exact member
    rw [equal]
    exact Space.inter _ targetMeasurable (Space.i_union_of_nat_injection _ (Tree.code fun _ _ => 0)
      (Tree.code_injective fun _ _ _ _ => rfl) _ (follows_measurable fields))

end TreeSpace

namespace StandardBorel

/-- Finite trees over standard-Borel fields are standard Borel. -/
@[expose] noncomputable def tree {fields : ∀ label, Space (Field label)}
    (presentations : ∀ label, StandardBorel (fields label)) : StandardBorel (Space.tree fields) :=
  ofEmbedding (TreeSpace.embedding fields)
    (piOfNatInjection Countable.Pair.encodeList Countable.Pair.encodeList_injective fun _ =>
      sum unit (sigma Fin.val (fun _ _ => Fin.ext) presentations))

end StandardBorel

end

end Problib.Measure
