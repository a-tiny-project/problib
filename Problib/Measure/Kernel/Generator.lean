module

public import Problib.Measure.Kernel.Basic
public import Problib.Measure.Additive.Partition
public import Problib.Measure.Dynkin.PiLambda

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u v
variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Construct a measurable kernel from a family of measures on a space generated
by a π-system, given pointwise finite measures, measurable total mass, and
measurable evaluations on generator members. -/
@[expose] public noncomputable def ofGenerator (family : α → Measure target)
    (finite : ∀ input, Measure.IsFinite (family input))
    (totalMeasurable : ENNRealMeasurable source (fun input => family input Set.univ))
    (generator : Set (Set β)) (generates : target = Space.generated generator)
    (pi : PiSystem generator)
    (basicMeasurable : ∀ set, generator set →
      ENNRealMeasurable source (fun input => family input set)) : Kernel source target where
  toFun := family
  measurable := by
    let property : DynkinSystem β := {
      Contains set := target.Measurable set ∧
        ENNRealMeasurable source (fun input => family input set)
      empty := by
        refine ⟨target.empty, ?_⟩
        have same : (fun input => family input Set.empty) = (fun _ => ENNReal.zero) :=
          funext fun input => (family input).empty_apply
        rw [same]
        exact ENNRealMeasurable.constant source ENNReal.zero
      complement := by
        rintro set ⟨measurable, values⟩
        refine ⟨target.complement measurable, ?_⟩
        have difference := ENNRealMeasurable.sub totalMeasurable values
        have same : (fun input => family input (Set.complement set)) =
            (fun input => ENNReal.sub (family input Set.univ) (family input set)) := by
          funext input
          rw [← (family input).add_complement measurable]
          exact (ENNReal.add_sub_cancel_left ((finite input).apply set)).symm
        rw [same]
        exact difference
      iUnion := by
        intro sets disjoint properties
        have measurable : ∀ index, target.Measurable (sets index) :=
          fun index => (properties index).1
        refine ⟨target.iUnion measurable, ?_⟩
        have series := ENNRealMeasurable.tsum (fun index => (properties index).2)
        have same : (fun input => family input (Set.iUnion sets)) =
            (fun input => ENNReal.tsum (fun index => family input (sets index))) := by
          funext input
          exact (family input).iUnion_disjoint sets measurable disjoint
        rw [same]
        exact series
    }
    intro set measurable
    have generated : (DynkinSystem.generated generator).Contains set :=
      (DynkinSystem.pi_lambda pi).mp (generates ▸ measurable)
    have included : property.Contains set := DynkinSystem.generated_minimal property (by
      intro basic member
      refine ⟨?_, basicMeasurable basic member⟩
      rw [generates]
      exact Space.generated_contains member) generated
    exact included.2

@[simp] public theorem ofGenerator_apply (family : α → Measure target)
    (finite : ∀ input, Measure.IsFinite (family input))
    (totalMeasurable : ENNRealMeasurable source (fun input => family input Set.univ))
    (generator : Set (Set β)) (generates : target = Space.generated generator)
    (pi : PiSystem generator)
    (basicMeasurable : ∀ set, generator set →
      ENNRealMeasurable source (fun input => family input set)) (input : α) :
    ofGenerator family finite totalMeasurable generator generates pi basicMeasurable input =
      family input := rfl

end Problib.Measure.Kernel
