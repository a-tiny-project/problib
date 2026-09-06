module

public import Foundations.Measure.Real.Borel
public import Foundations.Measure.Embedding

set_option autoImplicit false

namespace Foundations.Measure

universe u v

/-- A measurable space presented as a measurable subset of the Borel unit
interval. -/
public structure StandardBorel {alpha : Type u} (space : Space alpha) where
  range : Set Real.UnitInterval
  rangeMeasurable : Real.unitBorel.Measurable range
  equivalence : MeasurableEquivalence space
    (Space.comap
      (fun value : {point : Real.UnitInterval // range point} => value.val)
      Real.unitBorel)

namespace StandardBorel

variable {α : Type u} {space : Space α}

/-- Canonical measurable embedding of a standard-Borel space into the Borel
unit interval. -/
@[expose] public def embedding (presentation : StandardBorel space) :
    MeasurableEmbedding space Real.unitBorel :=
  presentation.equivalence.toEmbedding.trans
    (MeasurableEmbedding.subtype presentation.range presentation.rangeMeasurable)

/-- Canonical measurable embedding of a standard-Borel space into the real Borel
space, composing the unit-interval embedding with subtype inclusion into `Real`. -/
@[expose] public def embeddingReal (presentation : StandardBorel space) :
    MeasurableEmbedding space Real.borel :=
  presentation.embedding.trans
    (MeasurableEmbedding.subtype Real.unitSet
      (Real.measurable_Icc Foundations.Real.Construction.Dedekind.zero Foundations.Real.Construction.Dedekind.one))

/-- The range of the canonical embedding equals the presentation range set. -/
public theorem embedding_range (presentation : StandardBorel space) :
    Set.range presentation.embedding.function = presentation.range := by
  apply Set.ext
  intro output
  constructor
  · rintro ⟨input, equal⟩
    exact equal ▸ (presentation.equivalence.forward input).property
  · intro member
    let point : {input : Real.UnitInterval // presentation.range input} := ⟨output, member⟩
    refine ⟨presentation.equivalence.inverse point, ?_⟩
    change (presentation.equivalence.forward (presentation.equivalence.inverse point)).val = output
    rw [presentation.equivalence.forward_inverse]

/-- Transport a standard-Borel presentation along a measurable embedding. -/
@[expose] public noncomputable def ofEmbedding {β : Type v} {target : Space β}
    (embedding : MeasurableEmbedding space target) (presentation : StandardBorel target) :
    StandardBorel space := by
  let encoded := embedding.trans presentation.embedding
  exact {
    range := Set.range encoded.function
    rangeMeasurable := encoded.range_measurable
    equivalence := encoded.rangeEquivalence
  }

/-- Every measurable subset of the unit interval has its canonical
standard-Borel presentation. -/
@[expose] public def ofUnitIntervalSet
    (range : Set Real.UnitInterval)
    (rangeMeasurable : Real.unitBorel.Measurable range) :
    StandardBorel
      (Space.comap
        (fun value : {point : Real.UnitInterval // range point} => value.val)
        Real.unitBorel) where
  range := range
  rangeMeasurable := rangeMeasurable
  equivalence := MeasurableEquivalence.identity _

/-- The Borel unit interval is standard Borel. -/
@[expose] public def unitInterval :
    StandardBorel Real.unitBorel where
  range := Set.univ
  rangeMeasurable := Real.unitBorel.univ
  equivalence := {
    forward := fun value => ⟨value, True.intro⟩
    inverse := fun value => value.val
    inverse_forward := fun _ => rfl
    forward_inverse := by
      intro value
      cases value
      rfl
    forward_measurable := by
      unfold Space.comap
      apply MeasurableMap.intoGenerated
      rintro set ⟨target, targetMeasurable, rfl⟩
      have equal :
          Set.preimage
              (fun value : Real.UnitInterval => ⟨value, True.intro⟩)
              (Set.preimage
                (fun value :
                  {point : Real.UnitInterval //
                    (Set.univ : Set Real.UnitInterval) point} => value.val)
                target) =
            target := by
        apply Set.ext
        intro value
        rfl
      rw [equal]
      exact targetMeasurable
    inverse_measurable :=
      Space.comap_map
        (fun value :
          {point : Real.UnitInterval // (Set.univ : Set Real.UnitInterval) point} =>
            value.val)
        Real.unitBorel
  }

end StandardBorel

end Foundations.Measure
