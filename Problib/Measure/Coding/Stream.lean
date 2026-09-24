module

public import Problib.Real.Coding
public import Problib.Measure.Extended.Limit

set_option autoImplicit false

namespace Problib.Measure.Coding

open Problib.Real

universe u
variable {α : Type u} {source : Space α}

/-- Each weighted stream term is measurable when the coordinate events are measurable. -/
public theorem term_measurable {bits : α → Nat → Bool}
    (events : ∀ index, source.Measurable (fun value => bits value index = true))
    (index : Nat) :
    ENNRealMeasurable source (fun value => Real.Coding.term (bits value) index) := by
  classical
  have equal : (fun value => Real.Coding.term (bits value) index) =
      ennrealPiecewise (fun value => bits value index = true)
        (fun _ => Real.Coding.weight index) (fun _ => ENNReal.zero) := by
    funext value
    by_cases present : bits value index = true <;>
      simp [Real.Coding.term, ennrealPiecewise, present]
  rw [equal]
  exact ENNRealMeasurable.piecewise (events index)
    (ENNRealMeasurable.constant source (Real.Coding.weight index))
    (ENNRealMeasurable.constant source ENNReal.zero)

/-- The extended real encoding map is measurable when each coordinate event is measurable. -/
public theorem encode_measurable {bits : α → Nat → Bool}
    (events : ∀ index, source.Measurable (fun value => bits value index = true)) :
    ENNRealMeasurable source (fun value => Real.Coding.encode (bits value)) :=
  ENNRealMeasurable.tsum (term_measurable events)

/-- Reconstructed prefix sums are measurable functions on extended real Borel space. -/
public theorem decodedPrefix_measurable (count : Nat) :
    ENNRealMeasurable ennrealBorel (fun value => Real.Coding.decodedPrefix value count) := by
  classical
  induction count with
  | zero => exact ENNRealMeasurable.constant ennrealBorel ENNReal.zero
  | succ count induction =>
      exact ENNRealMeasurable.add induction
        (ENNRealMeasurable.piecewise
          (ENNRealMeasurable.le_set
            (ENNRealMeasurable.add induction
              (ENNRealMeasurable.constant ennrealBorel (Real.Coding.weight count)))
            ENNRealMeasurable.identity)
          (ENNRealMeasurable.constant ennrealBorel (Real.Coding.weight count))
          (ENNRealMeasurable.constant ennrealBorel ENNReal.zero))

/-- The recovered Boolean coordinate event is measurable in extended real Borel space. -/
public theorem digit_measurable (index : Nat) :
    ennrealBorel.Measurable (fun value => Real.Coding.digit value index = true) := by
  classical
  have equal : (fun value => Real.Coding.digit value index = true) =
      (fun value => ENNReal.le
        (ENNReal.add (Real.Coding.decodedPrefix value index) (Real.Coding.weight index)) value) := by
    apply Set.ext
    intro value
    simp only [Real.Coding.digit, decide_eq_true_eq]
  rw [equal]
  exact ENNRealMeasurable.le_set
    (ENNRealMeasurable.add (decodedPrefix_measurable index)
      (ENNRealMeasurable.constant ennrealBorel (Real.Coding.weight index)))
    ENNRealMeasurable.identity

end Problib.Measure.Coding
