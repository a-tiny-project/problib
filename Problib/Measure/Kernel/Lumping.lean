module
public import Problib.Measure.Kernel.Composition.Transport
public import Problib.Measure.Kernel.Scale
public import Problib.Measure.Space.Quotient
public import Problib.Measure.Kernel.Iteration.Lumping
public import Problib.Inference.Invariance

set_option autoImplicit false
namespace Problib.Measure
open Problib.Real Measure
open Problib.Inference
public section
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
  {space : Space α} {result : Space β}

namespace Kernel
/-- States in one fibre have the same image transition law. -/
@[expose] public def LumpsAlong (kernel : Kernel space space) (reduce : α → β)
    (reduceMeasurable : MeasurableMap space result reduce) : Prop :=
  ∀ left right, reduce left = reduce right →
    (kernel left).map reduce reduceMeasurable =
      (kernel right).map reduce reduceMeasurable

/-- A representative is selected only to evaluate a fibre-constant law. -/
@[expose] public noncomputable def lumped (kernel : Kernel space space)
    {reduce : α → β} (quotient : QuotientMap space result reduce)
    (lumps : kernel.LumpsAlong reduce quotient.measurable) : Kernel result result := by
  classical
  let representative := fun output => Classical.choose (quotient.surjective output)
  let imageLaw := fun output => (kernel (representative output)).map reduce quotient.measurable
  refine ⟨imageLaw, ?_⟩
  intro region regionMeasurable threshold
  apply quotient.final
  have equality : (fun input => imageLaw (reduce input) region) =
      (fun input => kernel input (Set.preimage reduce region)) := by
    funext input
    have fibre := lumps (representative (reduce input)) input
      (Classical.choose_spec (quotient.surjective (reduce input)))
    change ((kernel (representative (reduce input))).map reduce quotient.measurable) region =
      kernel input (Set.preimage reduce region)
    rw [fibre]
    exact Measure.map_apply _ _ _ regionMeasurable
  have measured := kernel.measurable (quotient.measurable regionMeasurable) threshold
  change space.Measurable
    (Set.preimage (fun input => imageLaw (reduce input) region)
      (ennrealIoi threshold))
  rw [equality]
  exact measured

public theorem lumped_map (kernel : Kernel space space)
    {reduce : α → β} (quotient : QuotientMap space result reduce)
    (lumps : kernel.LumpsAlong reduce quotient.measurable) (input : α) :
    (kernel input).map reduce quotient.measurable =
      Kernel.lumped kernel quotient lumps (reduce input) := by
  classical
  exact lumps input (Classical.choose (quotient.surjective (reduce input)))
    (Classical.choose_spec (quotient.surjective (reduce input))).symm

/-- A presented quotient step has fibre-constant image laws. -/
public theorem lumpsAlong_of_lumps (kernel : Kernel space space)
    {reduce : α → β} {reduceMeasurable : MeasurableMap space result reduce}
    (outputKernel : Kernel result result)
    (lumps : kernel.Lumps reduce reduceMeasurable outputKernel) :
    kernel.LumpsAlong reduce reduceMeasurable := by
  intro left right same
  calc
    (kernel left).map reduce reduceMeasurable = outputKernel (reduce left) := lumps left
    _ = outputKernel (reduce right) := by rw [same]
    _ = (kernel right).map reduce reduceMeasurable := (lumps right).symm

/-- A quotient map presents every fibre-constant image law as a step. -/
public theorem lumps_of_lumpsAlong (kernel : Kernel space space)
    {reduce : α → β} (quotient : QuotientMap space result reduce)
    (lumps : kernel.LumpsAlong reduce quotient.measurable) :
    kernel.Lumps reduce quotient.measurable
      (Kernel.lumped kernel quotient lumps) := by
  intro input
  exact Kernel.lumped_map kernel quotient lumps input

public theorem lumped_invariant (kernel : Kernel space space)
    {reduce : α → β} (quotient : QuotientMap space result reduce)
    (lumps : kernel.LumpsAlong reduce quotient.measurable)
    (target : Measure space) (invariant : KernelInvariant target kernel) :
    KernelInvariant (target.map reduce quotient.measurable)
      (Kernel.lumped kernel quotient lumps) := by
  unfold KernelInvariant at invariant ⊢
  have sameKernel :
      (Kernel.lumped kernel quotient lumps).precomp reduce quotient.measurable =
        kernel.map reduce quotient.measurable := by
    apply Kernel.ext
    intro input
    exact (lumped_map kernel quotient lumps input).symm
  calc
    (target.map reduce quotient.measurable).bind
        (Kernel.lumped kernel quotient lumps) =
        target.bind ((Kernel.lumped kernel quotient lumps).precomp reduce
          quotient.measurable) :=
      Measure.bind_map target reduce quotient.measurable _
    _ = target.bind (kernel.map reduce quotient.measurable) := by rw [sameKernel]
    _ = (target.bind kernel).map reduce quotient.measurable :=
      (Measure.map_bind target kernel reduce quotient.measurable).symm
    _ = target.map reduce quotient.measurable := by rw [invariant]

end Kernel

/-- A measurable relabelling preserving the quotient gives equal image laws. -/
public theorem lumpsAlong_of_equivariant {kernel : Kernel space space}
    {reduce : α → β} {reduceMeasurable : MeasurableMap space result reduce}
    (relabel : ∀ left right, reduce left = reduce right →
      ∃ output : α → α, ∃ outputMeasurable : MeasurableMap space space output,
        (∀ value, reduce (output value) = reduce value) ∧
          kernel right = (kernel left).map output outputMeasurable) :
    kernel.LumpsAlong reduce reduceMeasurable := by
  intro left right equal
  rcases relabel left right equal with ⟨output, measured, preserves, transition⟩
  rw [transition, Measure.map_comp]
  have same : (fun value => reduce (output value)) = reduce := by
    funext value
    exact preserves value
  apply Measure.ext
  intro region regionMeasurable
  rw [Measure.map_apply _ _ _ regionMeasurable,
    Measure.map_apply _ _ _ regionMeasurable]
  have preimages :
      Set.preimage (fun value => reduce (output value)) region =
        Set.preimage reduce region := by
    apply Set.ext
    intro value
    change region (reduce (output value)) ↔ region (reduce value)
    rw [preserves value]
  rw [preimages]

/-- A coupling whose two outputs share an image proves lumpability. -/
public theorem lumpsAlong_of_coupling {kernel : Kernel space space}
    {reduce : α → β} {reduceMeasurable : MeasurableMap space result reduce}
    (couple : ∀ left right, reduce left = reduce right →
      ∃ (Shared : Type w) (shared : Space Shared) (law : Measure shared)
        (first second : Shared → α)
        (firstMeasurable : MeasurableMap shared space first)
        (secondMeasurable : MeasurableMap shared space second),
        kernel left = law.map first firstMeasurable ∧
        kernel right = law.map second secondMeasurable ∧
        ∀ point, reduce (first point) = reduce (second point)) :
    kernel.LumpsAlong reduce reduceMeasurable := by
  intro left right same
  rcases couple left right same with
    ⟨Shared, shared, law, first, second, firstMeasured, secondMeasured,
      firstLaw, secondLaw, imageEqual⟩
  rw [firstLaw, secondLaw, Measure.map_comp, Measure.map_comp]
  have functions : (fun point => reduce (first point)) =
      (fun point => reduce (second point)) := funext imageEqual
  apply Measure.ext
  intro region regionMeasurable
  rw [Measure.map_apply _ _ _ regionMeasurable,
    Measure.map_apply _ _ _ regionMeasurable]
  apply congrArg (fun set => law set)
  apply Set.ext
  intro point
  change region (reduce (first point)) ↔ region (reduce (second point))
  rw [imageEqual point]


public theorem lumpsAlong_comp {first second : Kernel space space}
    {reduce : α → β} (quotient : QuotientMap space result reduce)
    (firstLumps : first.LumpsAlong reduce quotient.measurable)
    (secondLumps : second.LumpsAlong reduce quotient.measurable) :
    (first.comp second).LumpsAlong reduce quotient.measurable := by
  have secondKernel :
      second.map reduce quotient.measurable =
        (Kernel.lumped second quotient secondLumps).precomp reduce quotient.measurable := by
    apply Kernel.ext
    intro input
    exact Kernel.lumped_map second quotient secondLumps input
  have projected (input : α) :
      ((first.comp second) input).map reduce quotient.measurable =
        ((first input).map reduce quotient.measurable).bind
          (Kernel.lumped second quotient secondLumps) := by
    rw [Kernel.comp_apply, Measure.map_bind, secondKernel]
    exact (Measure.bind_map (first input) reduce quotient.measurable _).symm
  intro left right same
  calc
    ((first.comp second) left).map reduce quotient.measurable =
        ((first left).map reduce quotient.measurable).bind
          (Kernel.lumped second quotient secondLumps) := projected left
    _ = ((first right).map reduce quotient.measurable).bind
          (Kernel.lumped second quotient secondLumps) := by
      rw [firstLumps left right same]
    _ = ((first.comp second) right).map reduce quotient.measurable :=
      (projected right).symm

public theorem lumpsAlong_mixture {first second : Kernel space space}
    {reduce : α → β} {reduceMeasurable : MeasurableMap space result reduce}
    (firstLumps : first.LumpsAlong reduce reduceMeasurable)
    (secondLumps : second.LumpsAlong reduce reduceMeasurable)
    (firstWeight secondWeight : ENNReal) :
    (Kernel.add (Kernel.smul firstWeight first)
      (Kernel.smul secondWeight second)).LumpsAlong reduce reduceMeasurable := by
  intro left right same
  change (Measure.add
      (Measure.smul firstWeight (first left))
      (Measure.smul secondWeight (second left))).map reduce reduceMeasurable =
    (Measure.add
      (Measure.smul firstWeight (first right))
      (Measure.smul secondWeight (second right))).map reduce reduceMeasurable
  rw [Measure.map_add, Measure.map_add,
    Measure.map_smul, Measure.map_smul, Measure.map_smul, Measure.map_smul,
    firstLumps left right same, secondLumps left right same]
end
end Problib.Measure
