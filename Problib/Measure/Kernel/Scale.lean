module

public import Problib.Measure.Kernel.Basic
public import Problib.Algebra.Sum
public import Problib.Measure.Integral.Lebesgue.Basic
import Problib.Measure.Integral.Lebesgue.Measure

set_option autoImplicit false

/-!
# Scalar scaling of transition kernels

Defines scalar multiplication of transition kernels by extended nonnegative real
factors and proves preservation of global kernel finiteness.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Scalar multiplication of a transition kernel by an extended nonnegative real factor. -/
@[expose] public noncomputable def smul (factor : ENNReal) (kernel : Kernel source target) :
    Kernel source target where
  toFun := fun input => Measure.smul factor (kernel input)
  measurable := by
    intro set measurable
    have equal : (fun input => Measure.smul factor (kernel input) set) =
        (fun input => ENNReal.mul factor (kernel input set)) := by
      funext input
      exact Measure.smul_apply_measurable factor (kernel input) measurable
    rw [equal]
    exact (kernel.measurable measurable).const_mul factor

/-- Fiberwise evaluation of a scaled transition kernel. -/
@[simp] public theorem smul_apply (factor : ENNReal) (kernel : Kernel source target) (input : α) :
    smul factor kernel input = Measure.smul factor (kernel input) := rfl

/-- Scaling a globally finite transition kernel by a finite factor preserves global finiteness. -/
public theorem IsFinite.smul {kernel : Kernel source target} (finite : IsFinite kernel)
    (factor : ENNReal) (factorFinite : ENNReal.Finite factor) : IsFinite (Kernel.smul factor kernel) := by
  rcases finite.exists_bound with ⟨bound, boundFinite, bounded⟩
  refine ⟨⟨ENNReal.mul factor bound, ENNReal.mul_finite factorFinite boundFinite, ?_⟩⟩
  intro input
  rw [smul_apply, Measure.smul_apply_measurable _ _ target.univ]
  exact ENNReal.mul_le_mul (ENNReal.le_refl factor) (bounded input)

/-- Scaling an s-finite kernel by a finite factor scales each finite
component. -/
@[expose] public noncomputable def IsSFinite.smul {kernel : Kernel source target}
    (finite : IsSFinite kernel) (factor : ENNReal)
    (factorFinite : ENNReal.Finite factor) :
    IsSFinite (Kernel.smul factor kernel) where
  components := fun index => Kernel.smul factor (finite.components index)
  finite := fun index => (finite.finite index).smul factor factorFinite
  sum_eq := by
    apply Kernel.ext
    intro input
    apply Measure.ext
    intro set setMeasurable
    have whole : Kernel.sum finite.components input set = kernel input set := by
      rw [finite.sum_eq]
    have terms : (fun index =>
        Kernel.smul factor (finite.components index) input set) =
        fun index => ENNReal.mul factor (finite.components index input set) := by
      funext index
      rw [Kernel.smul_apply, Measure.smul_apply_measurable _ _ setMeasurable]
    rw [Kernel.sum_apply, Measure.sum_apply _ setMeasurable, terms,
      ENNReal.tsum_mul_left, Kernel.smul_apply,
      Measure.smul_apply_measurable _ _ setMeasurable, ← whole,
      Kernel.sum_apply, Measure.sum_apply _ setMeasurable]

/-- A fixed-weight mixture of two transition kernels. -/
@[expose] public noncomputable def mixture (weight : NNReal)
    (first second : Kernel source target) : Kernel source target :=
  Kernel.add
    (Kernel.smul (ENNReal.finite weight) first)
    (Kernel.smul (ENNReal.finite (NNReal.sub NNReal.one weight)) second)

/-- A finite fixed weighted sum of transition kernels. -/
@[expose] public noncomputable def weightedSum :
    List (NNReal × Kernel source target) → Kernel source target
  | [] => Kernel.zero source target
  | entry :: rest =>
      Kernel.add (Kernel.smul (ENNReal.finite entry.1) entry.2)
        (weightedSum rest)

/-- A fixed-weight mixture of s-finite kernels is s-finite. -/
@[expose] public noncomputable def IsSFinite.mixture (weight : NNReal)
    {first second : Kernel source target}
    (firstFinite : IsSFinite first) (secondFinite : IsSFinite second) :
    IsSFinite (mixture weight first second) :=
  IsSFinite.add (firstFinite.smul _ True.intro) (secondFinite.smul _ True.intro)

/-- A finite weighted sum of s-finite kernels is s-finite. -/
@[expose] public noncomputable def IsSFinite.weightedSum :
    (steps : List (NNReal × Kernel source target)) →
      (∀ entry, entry ∈ steps → IsSFinite entry.2) →
      IsSFinite (weightedSum steps)
  | [], _ => IsSFinite.zero source target
  | entry :: rest, finite =>
      IsSFinite.add ((finite entry (List.mem_cons_self ..)).smul _ True.intro)
        (IsSFinite.weightedSum rest
          (fun other member => finite other (List.mem_cons_of_mem _ member)))

/-- A fixed mixture of Markov kernels is Markov when its weight is at most one. -/
public theorem mixture_markov (weight : NNReal)
    (bounded : NNReal.le weight NNReal.one)
    (first second : Kernel source target)
    (firstMarkov : ∀ input, Measure.IsProbability (first input))
    (secondMarkov : ∀ input, Measure.IsProbability (second input))
    (input : α) : Measure.IsProbability (mixture weight first second input) := by
  constructor
  change Measure.add
      (Measure.smul (ENNReal.finite weight) (first input))
      (Measure.smul (ENNReal.finite (NNReal.sub NNReal.one weight))
        (second input)) Set.univ = ENNReal.one
  rw [Measure.add_apply_measurable _ _ target.univ,
    Measure.smul_apply_measurable _ _ target.univ,
    Measure.smul_apply_measurable _ _ target.univ,
    (firstMarkov input).univ_eq_one, (secondMarkov input).univ_eq_one,
    ENNReal.mul_one, ENNReal.mul_one]
  exact congrArg ENNReal.finite
    ((NNReal.add_comm weight (NNReal.sub NNReal.one weight)).trans
      (NNReal.sub_add_cancel bounded))

/-- A finite weighted sum of Markov kernels whose weights sum to one is
Markov. -/
public theorem weightedSum_markov (steps : List (NNReal × Kernel source target))
    (each : ∀ entry, entry ∈ steps → ∀ input,
      Measure.IsProbability (entry.2 input))
    (total : NNReal.additiveLaws.listSum (steps.map Prod.fst) = NNReal.one) (input : α) :
    Measure.IsProbability (weightedSum steps input) := by
  have mass : ∀ (current : List (NNReal × Kernel source target)),
      (∀ entry, entry ∈ current → ∀ input,
        Measure.IsProbability (entry.2 input)) →
      weightedSum current input Set.univ =
        ENNReal.finite (NNReal.additiveLaws.listSum (current.map Prod.fst)) := by
    intro current
    induction current with
    | nil =>
        intro _
        rw [weightedSum, zero_apply, Measure.zero_apply]
        rfl
    | cons entry rest induction =>
        intro markov
        rw [weightedSum, add_apply, Measure.add_apply_measurable _ _ target.univ,
          smul_apply, Measure.smul_apply_measurable _ _ target.univ,
          (markov entry (List.mem_cons_self ..) input).univ_eq_one, ENNReal.mul_one,
          induction (fun other member =>
            markov other (List.mem_cons_of_mem _ member))]
        rfl
  constructor
  rw [mass steps each, total]
  rfl

/-- Integrating against a finite weighted sum of kernels sums the weighted
integrals. -/
public theorem lintegral_weightedSum
    (steps : List (NNReal × Kernel source target)) (input : α) (function : β → ENNReal) :
    lintegral (Kernel.weightedSum steps input) function =
      ENNReal.additiveLaws.listSum (steps.map fun entry =>
        ENNReal.mul (ENNReal.finite entry.1) (lintegral (entry.2 input) function)) := by
  induction steps with
  | nil => exact lintegral_zero_measure function
  | cons entry rest induction =>
      show lintegral (Measure.add (Measure.smul (ENNReal.finite entry.1) (entry.2 input))
        (Kernel.weightedSum rest input)) function = _
      rw [lintegral_add_measure, lintegral_smul_measure, induction]
      rfl

end Problib.Measure.Kernel
