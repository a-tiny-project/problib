module

public import Problib.QuasiBorel.Sum
public import Problib.QuasiBorel.Measurable.Induced
public import Problib.Measure.Embedding.Sum

set_option autoImplicit false

/-!
# Induced measurable space of quasi-Borel sums

This module proves that the induced measurable functor preserves binary sums.
For every measurable random source, $L(A + B) = L(A) + L(B)$.
Summand injections also yield measurable embedding certificates.
-/
namespace Problib.QuasiBorel

public section

universe u v w

variable {Ω : Type u} {source : Problib.Measure.Space Ω}
  {left : Space.{u, v} (Source.ofMeasurable source)}
  {right : Space.{u, w} (Source.ofMeasurable source)}

/-- Proves that every accepted sum random element is measurable into
the direct sum of the induced measurable spaces. -/
theorem SumRandom.measurable {random : Ω → _root_.Sum left.Carrier right.Carrier}
    (accepted : SumRandom left right random) :
    Problib.Measure.MeasurableMap source
      (Problib.Measure.Space.sum left.toMeasurable right.toMeasurable) random := by
  induction accepted with
  | inl accepted =>
      exact Problib.Measure.MeasurableMap.comp
        (Problib.Measure.MeasurableMap.inl _ _) (Space.random_measurable accepted)
  | inr accepted =>
      exact Problib.Measure.MeasurableMap.comp
        (Problib.Measure.MeasurableMap.inr _ _) (Space.random_measurable accepted)
  | reparam measurable _ induction =>
      exact Problib.Measure.MeasurableMap.comp induction measurable
  | piecewise measurable _ induction =>
      exact Problib.Measure.MeasurableMap.countable_piecewise measurable induction

/-- Proves that the induced measurable space of a quasi-Borel sum is the direct
sum of the induced measurable spaces of its summands. -/
theorem Space.toMeasurable_sum
    (left : Space.{u, v} (Source.ofMeasurable source))
    (right : Space.{u, w} (Source.ofMeasurable source)) :
    (sum left right).toMeasurable =
      Problib.Measure.Space.sum left.toMeasurable right.toMeasurable := by
  apply Problib.Measure.Space.ext
  intro region
  constructor
  · intro measurable
    exact ⟨fun accepted => measurable (SumRandom.inl accepted),
      fun accepted => measurable (SumRandom.inr accepted)⟩
  · intro measurable random accepted
    exact accepted.measurable measurable

/-- Canonical left injection as a measurable embedding into the induced sum space. -/
@[expose] def Space.inlEmbedding
    (left : Space.{u, v} (Source.ofMeasurable source))
    (right : Space.{u, w} (Source.ofMeasurable source)) :
    Problib.Measure.MeasurableEmbedding left.toMeasurable (sum left right).toMeasurable where
  function := _root_.Sum.inl
  injective := fun _ _ equal => _root_.Sum.inl.inj equal
  measurable := (inl left right).toMeasurable
  image_measurable := by
    rw [toMeasurable_sum]
    exact (Problib.Measure.MeasurableEmbedding.inl _ _).image_measurable

/-- Canonical right injection as a measurable embedding into the induced sum space. -/
@[expose] def Space.inrEmbedding
    (left : Space.{u, v} (Source.ofMeasurable source))
    (right : Space.{u, w} (Source.ofMeasurable source)) :
    Problib.Measure.MeasurableEmbedding right.toMeasurable (sum left right).toMeasurable where
  function := _root_.Sum.inr
  injective := fun _ _ equal => _root_.Sum.inr.inj equal
  measurable := (inr left right).toMeasurable
  image_measurable := by
    rw [toMeasurable_sum]
    exact (Problib.Measure.MeasurableEmbedding.inr _ _).image_measurable

@[simp] theorem Space.inlEmbedding_apply
    (left : Space.{u, v} (Source.ofMeasurable source))
    (right : Space.{u, w} (Source.ofMeasurable source)) (value : left.Carrier) :
    (inlEmbedding left right).function value = _root_.Sum.inl value := rfl

@[simp] theorem Space.inrEmbedding_apply
    (left : Space.{u, v} (Source.ofMeasurable source))
    (right : Space.{u, w} (Source.ofMeasurable source)) (value : right.Carrier) :
    (inrEmbedding left right).function value = _root_.Sum.inr value := rfl

end

end Problib.QuasiBorel
