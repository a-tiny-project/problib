module
public import Problib.Measure.StandardBorel.Product
public import Problib.Measure.StandardBorel.Countable
public import Problib.Measure.StandardBorel.Pi
public import Problib.Measure.Embedding.Retraction
public import Problib.Measure.Configuration.Shape
public import Problib.Measure.Configuration.Canonical

set_option autoImplicit false

/-!
# Standard-Borel configuration spaces

Countable dependent sums, binary sums, finite lists and unordered finite
configurations of standard-Borel spaces are standard Borel.
-/

namespace Problib.Measure.StandardBorel
public section
universe u v

/-- Tag each component's unit-interval code with the component's natural
index. -/
@[expose] public noncomputable def sigmaEmbedding {ι : Type u} {β : ι → Type v}
    {spaces : ∀ index, Space (β index)} (code : ι → Nat)
    (injective : Function.Injective code)
    (presentations : ∀ index, StandardBorel (spaces index)) :
    MeasurableEmbedding (Space.sigma spaces)
      (Space.product (Space.discrete Nat) Real.unitBorel) where
  function := fun point =>
    (code point.1, (presentations point.1).embedding.function point.2)
  injective := by
    rintro ⟨first, left⟩ ⟨second, right⟩ equal
    have sameIndex : first = second := injective (congrArg Prod.fst equal)
    subst sameIndex
    have samePoint : left = right :=
      (presentations first).embedding.injective (congrArg Prod.snd equal)
    subst samePoint
    rfl
  measurable := by
    apply MeasurableMap.from_sigma_iff.mpr
    intro index
    exact Space.pair_measurable (MeasurableMap.constant _ _ (code index))
      (presentations index).embedding.measurable
  image_measurable := by
    classical
    intro region regionMeasurable
    let slice : Nat → Set Real.UnitInterval := fun tag output =>
      ∃ index, code index = tag ∧
        Set.image (presentations index).embedding.function
          (fun value => region ⟨index, value⟩) output
    have sliceMeasurable : ∀ tag, Real.unitBorel.Measurable (slice tag) := by
      intro tag
      by_cases tagged : ∃ index, code index = tag
      · obtain ⟨index, coded⟩ := tagged
        have equal : slice tag = Set.image (presentations index).embedding.function
            (fun value => region ⟨index, value⟩) := by
          apply Set.ext
          intro output
          constructor
          · rintro ⟨other, otherCoded, member⟩
            have same : other = index := injective (otherCoded.trans coded.symm)
            subst same
            exact member
          · intro member
            exact ⟨index, coded, member⟩
        rw [equal]
        exact (presentations index).embedding.image_measurable _ (regionMeasurable index)
      · have equal : slice tag = Set.empty :=
          Set.ext fun _ => ⟨fun ⟨index, coded, _⟩ => tagged ⟨index, coded⟩, False.elim⟩
        rw [equal]
        exact Real.unitBorel.empty
    have equal : Set.image (fun point : Sigma β =>
          (code point.1, (presentations point.1).embedding.function point.2)) region =
        Set.iUnion (fun tag =>
          Set.product (fun other : Nat => other = tag) (slice tag)) := by
      apply Set.ext
      rintro ⟨tag, output⟩
      constructor
      · rintro ⟨⟨index, value⟩, member, mapped⟩
        exact ⟨tag, rfl, index, congrArg Prod.fst mapped, value, member,
          congrArg Prod.snd mapped⟩
      · rintro ⟨other, sameTag, index, coded, value, member, mapped⟩
        refine ⟨⟨index, value⟩, member, ?_⟩
        change (code index, (presentations index).embedding.function value) =
          (tag, output)
        rw [coded, mapped, ← sameTag]
    rw [equal]
    exact (Space.product (Space.discrete Nat) Real.unitBorel).iUnion fun tag =>
      Space.product_set_measurable _ _ trivial (sliceMeasurable tag)

/-- A dependent sum over a countably coded index is standard Borel when each
component is. -/
@[expose] public noncomputable def sigma {ι : Type u} {β : ι → Type v}
    {spaces : ∀ index, Space (β index)} (code : ι → Nat)
    (injective : Function.Injective code)
    (presentations : ∀ index, StandardBorel (spaces index)) :
    StandardBorel (Space.sigma spaces) :=
  ofEmbedding (sigmaEmbedding code injective presentations)
    (product natural unitInterval)

/-- Tag the left summand's code with zero and the right summand's with one. -/
@[expose] public noncomputable def sumEmbedding {α : Type u} {β : Type v}
    {left : Space α} {right : Space β}
    (first : StandardBorel left) (second : StandardBorel right) :
    MeasurableEmbedding (Space.sum left right)
      (Space.product (Space.discrete Nat) Real.unitBorel) where
  function := Sum.elim (fun value => (0, first.embedding.function value))
    (fun value => (1, second.embedding.function value))
  injective := by
    rintro (leftValue | rightValue) (otherLeft | otherRight) equal
    · exact congrArg Sum.inl (first.embedding.injective (congrArg Prod.snd equal))
    · exact nomatch (congrArg Prod.fst equal : (0 : Nat) = 1)
    · exact nomatch (congrArg Prod.fst equal : (1 : Nat) = 0)
    · exact congrArg Sum.inr (second.embedding.injective (congrArg Prod.snd equal))
  measurable := MeasurableMap.sum_elim
    (Space.pair_measurable (MeasurableMap.constant _ _ 0) first.embedding.measurable)
    (Space.pair_measurable (MeasurableMap.constant _ _ 1) second.embedding.measurable)
  image_measurable := by
    intro region regionMeasurable
    have equal : Set.image (Sum.elim (fun value => ((0 : Nat), first.embedding.function value))
          (fun value => ((1 : Nat), second.embedding.function value))) region =
        Set.union
          (Set.product (fun tag : Nat => tag = 0)
            (Set.image first.embedding.function (Set.preimage Sum.inl region)))
          (Set.product (fun tag : Nat => tag = 1)
            (Set.image second.embedding.function (Set.preimage Sum.inr region))) := by
      apply Set.ext
      rintro ⟨tag, output⟩
      constructor
      · rintro ⟨point, member, mapped⟩
        cases point with
        | inl value =>
            exact Or.inl ⟨(congrArg Prod.fst mapped).symm, value, member,
              congrArg Prod.snd mapped⟩
        | inr value =>
            exact Or.inr ⟨(congrArg Prod.fst mapped).symm, value, member,
              congrArg Prod.snd mapped⟩
      · rintro (⟨tagged, value, member, mapped⟩ | ⟨tagged, value, member, mapped⟩)
        · refine ⟨Sum.inl value, member, ?_⟩
          exact Prod.ext tagged.symm mapped
        · refine ⟨Sum.inr value, member, ?_⟩
          exact Prod.ext tagged.symm mapped
    rw [equal]
    exact (Space.product (Space.discrete Nat) Real.unitBorel).union
      (Space.product_set_measurable _ _ trivial
        (first.embedding.image_measurable _ regionMeasurable.1))
      (Space.product_set_measurable _ _ trivial
        (second.embedding.image_measurable _ regionMeasurable.2))

/-- A binary sum of standard-Borel spaces is standard Borel. -/
@[expose] public noncomputable def sum {α : Type u} {β : Type v}
    {left : Space α} {right : Space β}
    (first : StandardBorel left) (second : StandardBorel right) :
    StandardBorel (Space.sum left right) :=
  ofEmbedding (sumEmbedding first second) (product natural unitInterval)

/-- Finite lists of a standard-Borel space are standard Borel, as the
countable sum of their coordinate powers. -/
@[expose] public noncomputable def list {α : Type v} {element : Space α}
    (presentation : StandardBorel element) : StandardBorel (Space.list element) :=
  ofEmbedding (listConfigurationEquivalence element).toEmbedding
    (sigma (spaces := (ConfigurationShapes.power element).space)
      (fun count : Nat => count) (fun _ _ equal => equal)
      (fun count => piOfNatInjection (fun index : Fin count => index.val)
        (fun _ _ equal => Fin.ext equal) (fun _ => presentation)))

/-- Unordered finite configurations of a standard-Borel space are standard
Borel. The canonical sorted list, keyed by the real embedding, codes each
configuration, and forgetting order decodes it. -/
@[expose] public noncomputable def unordered {α : Type v} {element : Space α}
    (presentation : StandardBorel element) :
    StandardBorel (Space.unordered element) :=
  ofRealLeftInverse
    (fun configuration => (list presentation).embeddingReal.function
      (canonical presentation.embeddingReal.function
        presentation.embeddingReal.injective configuration))
    (fun code => unorder ((list presentation).embeddingReal.retract [] code))
    (fun configuration => by
      change unorder ((list presentation).embeddingReal.retract []
          ((list presentation).embeddingReal.function
            (canonical presentation.embeddingReal.function
              presentation.embeddingReal.injective configuration))) = configuration
      rw [MeasurableEmbedding.retract_forward, unorder_canonical])
    (MeasurableMap.comp (list presentation).embeddingReal.measurable
      (canonical_measurable presentation.embeddingReal.function
        presentation.embeddingReal.injective presentation.embeddingReal.measurable))
    (MeasurableMap.comp (unorder_quotient_map element).measurable
      ((list presentation).embeddingReal.retract_measurable []))

end
end Problib.Measure.StandardBorel
