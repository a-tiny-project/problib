module

public import Problib.Measure.Disintegration.Reconstruction
public import Problib.Measure.Kernel.Product.Algebra
public import Problib.Measure.Kernel.Product.Piecewise
public import Problib.Measure.AlmostEverywhere.Transport

set_option autoImplicit false

namespace Problib.Measure.Measure.Disintegration

open Problib.Real

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {parameter : Space beta}
  {joint : Measure (Space.product source parameter)}

/-- Scaling a disintegrated joint measure by an extended scalar scales the second marginal and preserves the conditional kernel. -/
@[expose] public noncomputable def smul (selection : Disintegration joint) (factor : ENNReal) :
    Disintegration (Measure.smul factor joint) where
  conditional := selection.conditional
  conditionalSFinite := selection.conditionalSFinite
  reconstruction := by
    rw [Measure.Disintegrates, Measure.secondMarginal,
      Measure.map_smul factor joint Prod.snd (Space.second_measurable source parameter)]
    rw [Measure.reverseSemiproduct_smul]
    change Measure.smul factor (Measure.reverseSemiproduct (Measure.secondMarginal joint)
      selection.conditional selection.conditionalSFinite) = _
    rw [selection.reconstruction]

/-- Restricting a disintegrated joint measure to a preimage of a parameter region preserves the conditional kernel. -/
@[expose] public noncomputable def restrict (selection : Disintegration joint)
    {region : Set beta} (measurable : parameter.Measurable region) :
    Disintegration (joint.restrict (Set.preimage Prod.snd region)) where
  conditional := selection.conditional
  conditionalSFinite := selection.conditionalSFinite
  reconstruction := by
    rw [Disintegrates, secondMarginal_restrict_second joint measurable,
      ← reverseSemiproduct_restrict _ _ _ measurable, selection.reconstruction]

/-- Combine disintegrations of two parameter restrictions into a disintegration of the full joint measure via a piecewise conditional kernel. -/
@[expose] public noncomputable def piecewise (joint : Measure (Space.product source parameter))
    {region : Set beta} (measurable : parameter.Measurable region)
    (inside : Disintegration (joint.restrict (Set.preimage Prod.snd region)))
    (outside : Disintegration (joint.restrict (Set.preimage Prod.snd (Set.complement region)))) :
    Disintegration joint where
  conditional := Kernel.piecewise region measurable inside.conditional outside.conditional
  conditionalSFinite := inside.conditionalSFinite.piecewise outside.conditionalSFinite region measurable
  reconstruction := by
    change Measure.reverseSemiproduct (Measure.secondMarginal joint)
      (Kernel.piecewise region measurable inside.conditional outside.conditional)
      (inside.conditionalSFinite.piecewise outside.conditionalSFinite region measurable) = joint
    rw [reverseSemiproduct_piecewise,
      ← secondMarginal_restrict_second joint measurable, inside.reconstruction,
      ← secondMarginal_restrict_second joint (parameter.complement measurable), outside.reconstruction]
    exact restrict_add_complement joint (Space.second_measurable source parameter measurable)

/-- The piecewise conditional kernel has probability fibers almost everywhere when each component disintegration does. -/
public theorem piecewise_isProbability_ae (joint : Measure (Space.product source parameter))
    {region : Set beta} (measurable : parameter.Measurable region)
    (inside : Disintegration (joint.restrict (Set.preimage Prod.snd region)))
    (outside : Disintegration (joint.restrict (Set.preimage Prod.snd (Set.complement region))))
    (insideNormalized : (secondMarginal (joint.restrict (Set.preimage Prod.snd region))).AE
      (fun input => IsProbability (inside.conditional input)))
    (outsideNormalized : (secondMarginal (joint.restrict (Set.preimage Prod.snd (Set.complement region)))).AE
      (fun input => IsProbability (outside.conditional input))) :
    (secondMarginal joint).AE
      (fun input => IsProbability ((piecewise joint measurable inside outside).conditional input)) := by
  let predicate := fun input => IsProbability ((piecewise joint measurable inside outside).conditional input)
  rw [secondMarginal_restrict_second joint measurable] at insideNormalized
  rw [secondMarginal_restrict_second joint (parameter.complement measurable)] at outsideNormalized
  have insideHolds : ((secondMarginal joint).restrict region).AE predicate := by
    apply (insideNormalized.and ((secondMarginal joint).ae_restrict_mem measurable)).mono
    intro input both
    change IsProbability (Kernel.piecewise region measurable inside.conditional outside.conditional input)
    rw [Kernel.piecewise_apply_of_mem _ _ _ _ _ both.2]
    exact both.1
  have outsideHolds : ((secondMarginal joint).restrict (Set.complement region)).AE predicate := by
    apply (outsideNormalized.and ((secondMarginal joint).ae_restrict_mem
      (parameter.complement measurable))).mono
    intro input both
    change IsProbability (Kernel.piecewise region measurable inside.conditional outside.conditional input)
    rw [Kernel.piecewise_apply_of_not_mem _ _ _ _ _ both.2]
    exact both.1
  have combined := insideHolds.add outsideHolds
  rw [restrict_add_complement (secondMarginal joint) measurable] at combined
  exact combined

end Problib.Measure.Measure.Disintegration
