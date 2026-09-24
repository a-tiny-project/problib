module

public import Problib.Measure.Kernel.Precomp
public import Problib.Measure.Space.Sum

set_option autoImplicit false

/-!
# Binary coproducts of transition kernels

Constructs the universal copairing of transition kernels out of direct sums.
Proves computation laws, uniqueness, two-sided inverse identities, countable
sum distribution, and finiteness preservation.
-/
namespace Problib.Measure.Kernel

open Problib.Real

public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {left : Space α} {right : Space β} {target : Space γ} {result : Space δ}

/-- Universal copairing of transition kernels defined on the summands of a
direct sum space. -/
@[expose] noncomputable def copair (first : Kernel left target)
    (second : Kernel right target) : Kernel (Space.sum left right) target where
  toFun := Sum.elim first second
  measurable := fun measurable threshold =>
    ⟨first.measurable measurable threshold, second.measurable measurable threshold⟩

/-- Evaluate the copair kernel on a left summand injection. -/
@[simp] theorem copair_inl (first : Kernel left target) (second : Kernel right target)
    (input : α) : copair first second (Sum.inl input) = first input := rfl

/-- Evaluate the copair kernel on a right summand injection. -/
@[simp] theorem copair_inr (first : Kernel left target) (second : Kernel right target)
    (input : β) : copair first second (Sum.inr input) = second input := rfl

/-- Extensionality principle for transition kernels defined on direct sum
spaces. -/
theorem sum_ext {first second : Kernel (Space.sum left right) target}
    (inlEqual : ∀ input, first (Sum.inl input) = second (Sum.inl input))
    (inrEqual : ∀ input, first (Sum.inr input) = second (Sum.inr input)) :
    first = second := by
  apply Kernel.ext
  intro input
  cases input with
  | inl value => exact inlEqual value
  | inr value => exact inrEqual value

/-- Uniqueness of the copair kernel determined by its components on left and
right injections. -/
theorem copair_unique (first : Kernel left target) (second : Kernel right target)
    (candidate : Kernel (Space.sum left right) target)
    (inlEqual : ∀ input, candidate (Sum.inl input) = first input)
    (inrEqual : ∀ input, candidate (Sum.inr input) = second input) :
    candidate = copair first second := sum_ext inlEqual inrEqual

/-- Left precomposition retraction of the copair kernel. -/
@[simp] theorem copair_precomp_inl (first : Kernel left target) (second : Kernel right target) :
    (copair first second).precomp Sum.inl (MeasurableMap.inl left right) = first := by
  apply Kernel.ext
  intro input
  rfl

/-- Right precomposition retraction of the copair kernel. -/
@[simp] theorem copair_precomp_inr (first : Kernel left target) (second : Kernel right target) :
    (copair first second).precomp Sum.inr (MeasurableMap.inr left right) = second := by
  apply Kernel.ext
  intro input
  rfl

/-- Eta expansion of a kernel on a sum space from its left and right
precompositions. -/
@[simp] theorem copair_eta (kernel : Kernel (Space.sum left right) target) :
    copair (kernel.precomp Sum.inl (MeasurableMap.inl left right))
      (kernel.precomp Sum.inr (MeasurableMap.inr left right)) = kernel :=
  sum_ext (fun _ => rfl) (fun _ => rfl)

/-- Copairing distributes over countable sums in both component branches. -/
theorem copair_sum (first : Nat → Kernel left target) (second : Nat → Kernel right target) :
    copair (Kernel.sum first) (Kernel.sum second) =
      Kernel.sum (fun index => copair (first index) (second index)) :=
  sum_ext (fun _ => rfl) (fun _ => rfl)

/-- Copairing commutes with target pushforward of transition kernels. -/
theorem copair_map (first : Kernel left target) (second : Kernel right target)
    (function : γ → δ) (measurable : MeasurableMap target result function) :
    (copair first second).map function measurable =
      copair (first.map function measurable) (second.map function measurable) :=
  sum_ext (fun _ => rfl) (fun _ => rfl)

/-- Copairing preserves uniform finiteness using the sum of the branch
bounds. -/
theorem IsFinite.copair {first : Kernel left target} {second : Kernel right target}
    (firstFinite : IsFinite first) (secondFinite : IsFinite second) :
    IsFinite (Kernel.copair first second) := by
  rcases firstFinite.exists_bound with ⟨firstBound, firstBoundFinite, firstBounded⟩
  rcases secondFinite.exists_bound with ⟨secondBound, secondBoundFinite, secondBounded⟩
  refine ⟨⟨ENNReal.add firstBound secondBound,
    ENNReal.add_finite firstBoundFinite secondBoundFinite, ?_⟩⟩
  intro input
  cases input with
  | inl value =>
    apply ENNReal.le_trans (firstBounded value)
    simpa only [ENNReal.add_zero] using
      ENNReal.add_le_add_left (ENNReal.zero_le secondBound) firstBound
  | inr value =>
    apply ENNReal.le_trans (secondBounded value)
    simpa only [ENNReal.zero_add] using
      ENNReal.add_le_add_right (ENNReal.zero_le firstBound) secondBound

/-- Characterize uniform finiteness of a copair kernel by finiteness of both
branches. -/
theorem isFinite_copair_iff {first : Kernel left target} {second : Kernel right target} :
    IsFinite (copair first second) ↔ IsFinite first ∧ IsFinite second := by
  constructor
  · intro finite
    constructor
    · simpa only [copair_precomp_inl] using
        finite.precomp Sum.inl (MeasurableMap.inl left right)
    · simpa only [copair_precomp_inr] using
        finite.precomp Sum.inr (MeasurableMap.inr left right)
  · rintro ⟨firstFinite, secondFinite⟩
    exact firstFinite.copair secondFinite

/-- Copairing preserves s-finiteness by pairing component sequences
termwise. -/
noncomputable def IsSFinite.copair {first : Kernel left target} {second : Kernel right target}
    (firstFinite : IsSFinite first) (secondFinite : IsSFinite second) :
    IsSFinite (Kernel.copair first second) where
  components := fun index => Kernel.copair
    (firstFinite.components index) (secondFinite.components index)
  finite := fun index => (firstFinite.finite index).copair (secondFinite.finite index)
  sum_eq := by
    rw [← copair_sum, firstFinite.sum_eq, secondFinite.sum_eq]

end

end Problib.Measure.Kernel
