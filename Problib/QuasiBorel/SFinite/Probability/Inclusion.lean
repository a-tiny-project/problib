import Problib.QuasiBorel.Probability.Random
import Problib.QuasiBorel.SFinite.Random
import Problib.Measure.Giry.Kernel

/-!
# Injective inclusion of probability laws into s-finite laws

This module constructs the canonical injective quasi-Borel morphism from
probability laws to represented s-finite laws. It converts Giry probability
presentations into s-finite presentations while preserving the underlying measure
and total mass one.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)
open Problib.Real (ENNReal)

universe u

variable {space : Space.{0, u} realSource}

/-- Injection of a probability law into the space of representable s-finite laws. -/
noncomputable def ofProbability (law : Probability.Law space) : Law space := by
  refine ⟨law.val.val, ?_⟩
  refine ⟨Presentation.total law.presentation.random law.presentation.accepted
    law.presentation.sourceLaw.val (Measure.SFinite.ofFinite law.presentation.sourceLaw.property.to_finite), ?_⟩
  rw [Presentation.total_toMeasure]
  exact congrArg Subtype.val law.presentation_toGiry

@[simp] theorem ofProbability_val (law : Probability.Law space) :
    (ofProbability law).val = law.val.val := rfl

/-- Canonical quasi-Borel morphism embedding probability laws into s-finite laws. -/
noncomputable def ofProbabilityHom (space : Space.{0, u} realSource) :
    Hom (Probability.object space) (object space) where
  toFun := ofProbability
  map_random := by
    intro random accepted
    let family := Classical.choice accepted
    refine ⟨{
      random := fun seed => Sum.inr (family.random seed)
      accepted := SumRandom.inr family.accepted
      kernel := Giry.toKernel family.kernel family.measurable
      sfinite := (Giry.toKernel_finite family.kernel family.measurable).toSFinite
      law := ?_
    }⟩
    intro seed
    change (Presentation.total family.random family.accepted (family.kernel seed).val
      (Measure.SFinite.ofFinite (family.kernel seed).property.to_finite)).toMeasure = _
    rw [Presentation.total_toMeasure]
    exact congrArg Subtype.val (family.law seed)

@[simp] theorem ofProbabilityHom_apply (law : Probability.Law space) :
    ofProbabilityHom space law = ofProbability law := rfl

/-- The canonical embedding of probability laws into s-finite laws is injective. -/
theorem ofProbability_injective : Function.Injective (@ofProbability space) := by
  intro left right equal
  apply Probability.Law.ext
  apply Subtype.ext
  exact congrArg (fun current : Law space => current.val) equal

theorem ofProbability_probability (law : Probability.Law space) :
    Measure.IsProbability (ofProbability law).val := law.val.property

@[simp] theorem ofProbability_univ (law : Probability.Law space) :
    (ofProbability law).val Set.univ = ENNReal.one := law.val.property.univ_eq_one

end Problib.QuasiBorel.SFinite
