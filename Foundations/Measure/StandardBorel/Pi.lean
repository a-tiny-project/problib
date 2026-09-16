module

public import Foundations.Measure.Coding.Sequence
public import Foundations.Measure.StandardBorel.Countable
public import Foundations.Measure.StandardBorel.Retraction

set_option autoImplicit false

namespace Foundations.Measure.StandardBorel

open Foundations.Measure.Real (borel unitBorel unitZero)

universe u v

variable {ι : Type u} {alpha : ι → Type v} {spaces : ∀ index, Space (alpha index)}

private noncomputable def coordinates (code : ι → Nat)
    (presentations : ∀ index, StandardBorel (spaces index))
    (point : ∀ index, alpha index) (index : Nat) : Real.UnitInterval := by
  classical
  exact if represented : ∃ coordinate, code coordinate = index then
    (presentations (Classical.choose represented)).embedding.function
      (point (Classical.choose represented))
  else unitZero

private theorem coordinates_index (code : ι → Nat) (injective : Function.Injective code)
    (presentations : ∀ index, StandardBorel (spaces index))
    (point : ∀ index, alpha index) (index : ι) :
    coordinates code presentations point (code index) = (presentations index).embedding.function (point index) := by
  classical
  have represented : ∃ coordinate, code coordinate = code index := ⟨index, rfl⟩
  have chosen : Classical.choose represented = index := injective (Classical.choose_spec represented)
  simp only [coordinates, dif_pos represented]
  exact congrArg (fun coordinate =>
    (presentations coordinate).embedding.function (point coordinate)) chosen

private theorem coordinates_measurable (code : ι → Nat)
    (presentations : ∀ index, StandardBorel (spaces index)) :
    MeasurableMap (Space.pi spaces) (Space.pi (fun _ : Nat => unitBorel))
      (coordinates code presentations) := by
  classical
  apply Space.pi_measurable
  intro index
  by_cases represented : ∃ coordinate, code coordinate = index
  · simpa only [coordinates, dif_pos represented] using
      MeasurableMap.comp (presentations (Classical.choose represented)).embedding.measurable
        (Space.coordinate_measurable spaces (Classical.choose represented))
  · simpa only [coordinates, dif_neg represented] using
      MeasurableMap.constant (Space.pi spaces) unitBorel unitZero

/-- Standard Borel presentation for the countable product of Borel unit
intervals. -/
@[expose] public noncomputable def unitSequence :
    StandardBorel (Space.pi (fun _ : Nat => unitBorel)) :=
  ofRealLeftInverse Coding.Sequence.encode Coding.Sequence.decode Coding.Sequence.decode_encode
    Coding.Sequence.encode_measurable Coding.Sequence.decode_measurable

/-- Standard Borel presentation for product spaces whose index type injects into
the natural numbers.
The construction accepts per-factor standard-Borel presentations and handles
empty product carriers without global inhabitant hypotheses. -/
public noncomputable def piOfNatInjection (code : ι → Nat)
    (injective : Function.Injective code) (presentations : ∀ index, StandardBorel (spaces index)) :
    StandardBorel (Space.pi spaces) := by
  classical
  by_cases inhabited : Nonempty (∀ index, alpha index)
  · let fallback := Classical.choice inhabited
    refine ofRealLeftInverse
      (fun point => Coding.Sequence.encode (coordinates code presentations point))
      (fun seed index => (presentations index).embedding.retract (fallback index)
        (Coding.Sequence.decode seed (code index))) ?_ ?_ ?_
    · intro point
      funext index
      rw [Coding.Sequence.decode_encode, coordinates_index code injective presentations point index]
      exact (presentations index).embedding.retract_forward (fallback index) (point index)
    · exact MeasurableMap.comp Coding.Sequence.encode_measurable (coordinates_measurable code presentations)
    · apply Space.pi_measurable
      intro index
      exact MeasurableMap.comp ((presentations index).embedding.retract_measurable (fallback index))
        (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Nat => unitBorel) (code index))
          Coding.Sequence.decode_measurable)
  · exact ofEmpty inhabited

/-- Standard Borel presentation for countable Nat-indexed product spaces. -/
@[expose] public noncomputable def countableProduct {beta : Nat → Type v}
    {targets : ∀ index, Space (beta index)} (presentations : ∀ index, StandardBorel (targets index)) :
    StandardBorel (Space.pi targets) :=
  piOfNatInjection (fun index => index) (fun _ _ equal => equal) presentations

/-- Standard Borel presentation for the countable sequence space of real
Borel spaces. -/
@[expose] public noncomputable def realSequence :
    StandardBorel (Space.pi (fun _ : Nat => borel)) :=
  countableProduct (fun _ => real)

end Foundations.Measure.StandardBorel
