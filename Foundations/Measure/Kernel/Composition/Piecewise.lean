module

public import Foundations.Measure.Kernel.Composition.Transport
public import Foundations.Measure.Kernel.Sum
public import Foundations.Measure.Kernel.Piecewise.Countable
public import Foundations.Measure.Additive.Comap.Sum

set_option autoImplicit false

/-!
# Composition laws for copair and piecewise transition kernels

Establishes composition and bind distribution for copairs and countable
piecewise kernels. Proves zero-extended branch representations using the
existing zero kernel.
-/
namespace Foundations.Measure

public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {left : Space α} {right : Space β} {target : Space γ} {result : Space δ}

namespace Measure

/-- Distribute measure bind over a copair kernel into the sum of the summand
pullback binds. -/
theorem bind_copair (measure : Measure (Space.sum left right))
    (first : Kernel left target) (second : Kernel right target) :
    measure.bind (Kernel.copair first second) =
      Measure.add ((measure.comap (MeasurableEmbedding.inl left right)).bind first)
        ((measure.comap (MeasurableEmbedding.inr left right)).bind second) := by
  calc
    measure.bind (Kernel.copair first second) =
        (Measure.add
          ((measure.comap (MeasurableEmbedding.inl left right)).map
            Sum.inl (MeasurableMap.inl left right))
          ((measure.comap (MeasurableEmbedding.inr left right)).map
            Sum.inr (MeasurableMap.inr left right))).bind (Kernel.copair first second) :=
      congrArg (fun current => current.bind (Kernel.copair first second))
        (coproduct_decomposition measure).symm
    _ = _ := by
      rw [add_bind, bind_map, bind_map, Kernel.copair_precomp_inl, Kernel.copair_precomp_inr]

/-- Express left summand pullback bind as an ambient bind with right zero
extension. -/
theorem bind_comap_inl (measure : Measure (Space.sum left right))
    (kernel : Kernel left target) :
    (measure.comap (MeasurableEmbedding.inl left right)).bind kernel =
      measure.bind (Kernel.copair kernel (Kernel.zero right target)) := by
  have supported := bind_comap_of_zero_outside measure (MeasurableEmbedding.inl left right)
    (Kernel.copair kernel (Kernel.zero right target)) (by
      intro input outside
      cases input with
      | inl value => exact False.elim (outside ⟨value, rfl⟩)
      | inr _ => rfl)
  change (measure.comap (MeasurableEmbedding.inl left right)).bind
    ((Kernel.copair kernel (Kernel.zero right target)).precomp
      Sum.inl (MeasurableMap.inl left right)) = _ at supported
  simpa only [Kernel.copair_precomp_inl] using supported

/-- Express right summand pullback bind as an ambient bind with left zero
extension. -/
theorem bind_comap_inr (measure : Measure (Space.sum left right))
    (kernel : Kernel right target) :
    (measure.comap (MeasurableEmbedding.inr left right)).bind kernel =
      measure.bind (Kernel.copair (Kernel.zero left target) kernel) := by
  have supported := bind_comap_of_zero_outside measure (MeasurableEmbedding.inr left right)
    (Kernel.copair (Kernel.zero left target) kernel) (by
      intro input outside
      cases input with
      | inl _ => rfl
      | inr value => exact False.elim (outside ⟨value, rfl⟩))
  change (measure.comap (MeasurableEmbedding.inr left right)).bind
    ((Kernel.copair (Kernel.zero left target) kernel).precomp
      Sum.inr (MeasurableMap.inr left right)) = _ at supported
  simpa only [Kernel.copair_precomp_inr] using supported

end Measure

namespace Kernel

/-- Distribute kernel composition on the right across a copair kernel. -/
theorem copair_comp (first : Kernel left target) (second : Kernel right target)
    (after : Kernel target result) :
    (copair first second).comp after = copair (first.comp after) (second.comp after) :=
  sum_ext (fun _ => rfl) (fun _ => rfl)

/-- Distribute kernel composition on the left across a copair kernel into the
sum of pulled-back compositions. -/
theorem comp_copair (before : Kernel result (Space.sum left right))
    (first : Kernel left target) (second : Kernel right target) :
    before.comp (copair first second) =
      Kernel.add ((before.comap (MeasurableEmbedding.inl left right)).comp first)
        ((before.comap (MeasurableEmbedding.inr left right)).comp second) := by
  apply Kernel.ext
  intro input
  exact Measure.bind_copair (before input) first second

/-- Express left pullback composition as ambient composition with right zero
extension. -/
theorem comp_copair_zero (before : Kernel result (Space.sum left right))
    (after : Kernel left target) :
    (before.comap (MeasurableEmbedding.inl left right)).comp after =
      before.comp (copair after (Kernel.zero right target)) := by
  apply Kernel.ext
  intro input
  exact Measure.bind_comap_inl (before input) after

/-- Express right pullback composition as ambient composition with left zero
extension. -/
theorem comp_zero_copair (before : Kernel result (Space.sum left right))
    (after : Kernel right target) :
    (before.comap (MeasurableEmbedding.inr left right)).comp after =
      before.comp (copair (Kernel.zero left target) after) := by
  apply Kernel.ext
  intro input
  exact Measure.bind_comap_inr (before input) after

/-- Distribute kernel composition on the right across countable piecewise
selection. -/
theorem countablePiecewise_comp (partition : α → Nat)
    (measurable : ∀ index, left.Measurable (fun input => partition input = index))
    (kernels : Nat → Kernel left target) (after : Kernel target result) :
    (countablePiecewise partition measurable kernels).comp after =
      countablePiecewise partition measurable (fun index => (kernels index).comp after) := by
  apply Kernel.ext
  intro input
  rfl

end Kernel

end

end Foundations.Measure
