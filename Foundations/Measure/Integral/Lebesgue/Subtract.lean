module

public import Foundations.Measure.Integral.Lebesgue.AlmostEverywhere
public import Foundations.Measure.Extended.Algebra.Binary

set_option autoImplicit false

namespace Foundations.Measure

open Foundations.Real

universe u

variable {α : Type u} {space : Space α}

/-- Lower integration distributes over measurable subtraction under
almost-everywhere domination and finite integral of the subtracted function. -/
public theorem lintegral_sub_ae (measure : Measure space) {left right : α → ENNReal}
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right)
    (rightFinite : ENNReal.Finite (lintegral measure right))
    (included : measure.AE (fun input => ENNReal.le (right input) (left input))) :
    lintegral measure (fun input => ENNReal.sub (left input) (right input)) =
      ENNReal.sub (lintegral measure left) (lintegral measure right) := by
  have partition : ENNReal.add
      (lintegral measure (fun input => ENNReal.sub (left input) (right input)))
      (lintegral measure right) = lintegral measure left := by
    rw [← lintegral_add measure (ENNRealMeasurable.sub leftMeasurable rightMeasurable) rightMeasurable]
    exact lintegral_congr_ae (included.mono (fun _ bound => ENNReal.subAddCancel bound))
  rw [← partition, ENNReal.addSubCancelRight rightFinite]

/-- Lower integration distributes over measurable subtraction under pointwise
domination and finite integral of the subtracted function. -/
public theorem lintegral_sub (measure : Measure space) {left right : α → ENNReal}
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right)
    (rightFinite : ENNReal.Finite (lintegral measure right))
    (included : ∀ input, ENNReal.le (right input) (left input)) :
    lintegral measure (fun input => ENNReal.sub (left input) (right input)) =
      ENNReal.sub (lintegral measure left) (lintegral measure right) :=
  lintegral_sub_ae measure leftMeasurable rightMeasurable rightFinite
    (Measure.ae_of_forall included)

end Foundations.Measure
