module

public import Foundations.Measure.Kernel.Comap
public import Foundations.Measure.Kernel.Composition.Bind
public import Foundations.Measure.Embedding.Sum

set_option autoImplicit false

/-!
# Necessity of support hypotheses for unrestricted source pullback bind identities

Witnesses that omitting support conditions falsifies unrestricted source
pullback bind identities through generic Dirac measures and concrete two-Unit
coproducts. The exact identity with range restriction always holds.
-/
namespace Foundations.Measure.Kernel.Composition.Necessity

open Foundations.Real

public section

universe u v w

/-- Witness that binding after source pullback of a Dirac measure outside the
embedding range fails to equal the ambient bind against the constant
continuation. -/
theorem source_comap_bind_needs_support
    {α : Type u} {β : Type v} {γ : Type w}
    {source : Space α} {middle : Space β} {target : Space γ}
    (embedding : MeasurableEmbedding source middle) (omitted : β)
    (outside : ¬Set.range embedding.function omitted) (output : γ) :
    ((Measure.dirac middle omitted).comap embedding).bind
        (Kernel.const source (Measure.dirac target output)) ≠
      (Measure.dirac middle omitted).bind
        (Kernel.const middle (Measure.dirac target output)) := by
  classical
  have pulled : (Measure.dirac middle omitted).comap embedding = Measure.zero source := by
    apply (Measure.eq_zero_iff_univ_eq_zero _).mpr
    rw [Measure.comap_apply_univ,
      Measure.dirac_apply middle omitted embedding.range_measurable]
    exact if_neg outside
  rw [pulled, Measure.zero_bind, Measure.dirac_bind, Kernel.const_apply]
  intro equal
  have total := congrArg (fun measure : Measure target => measure Set.univ) equal
  rw [Measure.zero_apply, Measure.dirac_apply_univ] at total
  exact ENNReal.oneNeZero total.symm

/-- Concrete counterexample on a two-Unit direct sum space proving source
pullback bind fails without support hypotheses. -/
theorem sum_source_comap_bind_needs_support :
    ((Measure.dirac (Space.sum (Space.discrete Unit) (Space.discrete Unit))
        (Sum.inl ())).comap
          (MeasurableEmbedding.inr (Space.discrete Unit) (Space.discrete Unit))).bind
        (Kernel.const (Space.discrete Unit) (Measure.dirac (Space.discrete Unit) ())) ≠
      (Measure.dirac (Space.sum (Space.discrete Unit) (Space.discrete Unit))
        (Sum.inl ())).bind
        (Kernel.const (Space.sum (Space.discrete Unit) (Space.discrete Unit))
          (Measure.dirac (Space.discrete Unit) ())) := by
  apply source_comap_bind_needs_support
  rintro ⟨input, equal⟩
  cases equal

end

end Foundations.Measure.Kernel.Composition.Necessity
