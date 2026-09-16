import Foundations.Measure.Giry.Monad
import Foundations.Measure.Kernel.Distribution.Bounds
import Foundations.Measure.Kernel.Randomization.Unit
import Foundations.Measure.StandardBorel.Pi

set_option autoImplicit false

namespace Foundations.Measure.Giry

open Foundations.Measure.Real (unitBorel UnitInterval unitZero unitRationalBasis)

universe u

private noncomputable def unitCoordinates (law : Law unitBorel) : Nat → UnitInterval :=
  fun index => Kernel.Randomizer.Unit.bounds (evaluationKernel unitBorel) index law

private theorem unitCoordinates_measurable :
    MeasurableMap (space unitBorel) (Space.pi (fun _ : Nat => unitBorel)) unitCoordinates :=
  Space.pi_measurable (fun index => Kernel.Randomizer.Unit.bounds_measurable (evaluationKernel unitBorel) index)

private noncomputable def unitBoundsKernel :
    Kernel (Space.pi (fun _ : Nat => unitBorel)) unitBorel :=
  Kernel.ofDistributionBounds unitRationalBasis (fun index point => point index)
    (fun index => Space.coordinate_measurable (fun _ : Nat => unitBorel) index)

private theorem unitBoundsKernel_probability (point : Nat → UnitInterval) :
    Measure.IsProbability (unitBoundsKernel point) := by
  change Measure.IsProbability
    (Real.DistributionFunction.ofUpperBounds unitRationalBasis point).measure
  exact (Real.DistributionFunction.ofUpperBounds unitRationalBasis point).measure_isProbability

private noncomputable def fromUnitCoordinates : (Nat → UnitInterval) → Law unitBorel :=
  ofKernel unitBoundsKernel unitBoundsKernel_probability

private theorem fromUnitCoordinates_measurable :
    MeasurableMap (Space.pi (fun _ : Nat => unitBorel)) (space unitBorel) fromUnitCoordinates :=
  ofKernel_measurable unitBoundsKernel unitBoundsKernel_probability

private theorem fromUnitCoordinates_unitCoordinates (law : Law unitBorel) :
    fromUnitCoordinates (unitCoordinates law) = law := by
  apply Subtype.ext
  change (Kernel.Randomizer.Unit.distribution (evaluationKernel unitBorel) law).measure = law.val
  exact Kernel.Randomizer.Unit.distribution_measure (evaluationKernel unitBorel) (fun law => law.property) law

/-- Standard Borel presentation of the Giry probability law space on the
unit interval.
Rational-interval masses determine the law, reconstructed measurably through
coordinate sequences and upper distribution bounds. -/
noncomputable def unitInterval_standardBorel :
    Foundations.Measure.StandardBorel (space unitBorel) := by
  refine Foundations.Measure.StandardBorel.ofRealLeftInverse
    (fun law => Coding.Sequence.encode (unitCoordinates law))
    (fun seed => fromUnitCoordinates (Coding.Sequence.decode seed)) ?_
    (MeasurableMap.comp Coding.Sequence.encode_measurable unitCoordinates_measurable)
    (MeasurableMap.comp fromUnitCoordinates_measurable Coding.Sequence.decode_measurable)
  intro law
  rw [Coding.Sequence.decode_encode]
  exact fromUnitCoordinates_unitCoordinates law

/-- Standard Borel presentation of the Giry probability law space on any
standard-Borel space.
The presentation transfers through the standard-Borel embedding and retraction
into the unit interval, handling empty carriers without global inhabitant
hypotheses. -/
noncomputable def standardBorel {alpha : Type u} {source : Space alpha}
    (presentation : Foundations.Measure.StandardBorel source) :
    Foundations.Measure.StandardBorel (space source) := by
  classical
  by_cases inhabited : Nonempty alpha
  · let fallback := Classical.choice inhabited
    let unitEmbedding := unitInterval_standardBorel.embeddingReal
    let unitFallback := pure unitBorel unitZero
    refine Foundations.Measure.StandardBorel.ofRealLeftInverse
      (fun law => unitEmbedding.function (map presentation.embedding.function presentation.embedding.measurable law))
      (fun seed => map (presentation.embedding.retract fallback) (presentation.embedding.retract_measurable fallback)
        (unitEmbedding.retract unitFallback seed)) ?_ ?_ ?_
    · intro law
      rw [unitEmbedding.retract_forward, map_comp]
      have inverse : (fun point => presentation.embedding.retract fallback
          (presentation.embedding.function point)) = (fun point => point) :=
        funext (presentation.embedding.retract_forward fallback)
      simpa only [inverse] using (map_id law)
    · exact MeasurableMap.comp unitEmbedding.measurable
        (map_measurable presentation.embedding.function presentation.embedding.measurable)
    · exact MeasurableMap.comp
        (map_measurable (presentation.embedding.retract fallback) (presentation.embedding.retract_measurable fallback))
        (unitEmbedding.retract_measurable unitFallback)
  · apply Foundations.Measure.StandardBorel.ofEmpty
    rintro ⟨law⟩
    exact inhabited law.property.nonempty

end Foundations.Measure.Giry
