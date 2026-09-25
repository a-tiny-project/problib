module

public import Problib.Measure.Disintegration.Reconstruction
public import Problib.Measure.Integral.Density.Basic
public import Problib.Measure.AlmostEverywhere.Basic
import Problib.Measure.Integral.Density.Uniqueness

set_option autoImplicit false

namespace Problib.Measure.Measure.Disintegration

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {parameter : Space beta}
  {joint : Measure (Space.product source parameter)}

/-- The conditional evaluations of a fixed measurable event form a density of
the restricted second marginal relative to the full second marginal.
Requires only an exact disintegration and measurability of the conditioned set.
Requires no σ-finiteness or standard-Borel presentation. -/
public theorem conditional_isDensity (selection : Disintegration joint)
    {set : Set alpha} (measurable : source.Measurable set) :
    IsDensity (secondMarginal (joint.restrict (Set.preimage Prod.fst set)))
      (secondMarginal joint) (fun input => selection.conditional input set) := by
  apply Measure.ext
  intro region regionMeasurable
  rw [secondMarginal_apply _ regionMeasurable,
    joint.restrict_apply _ (Space.second_measurable source parameter regionMeasurable),
    Measure.withDensity_apply _ _ regionMeasurable]
  have rectangle : Set.inter (Set.preimage Prod.snd region) (Set.preimage Prod.fst set) =
      Set.product set region := by
    apply Set.ext
    intro value
    exact ⟨fun member => ⟨member.2, member.1⟩, fun member => ⟨member.2, member.1⟩⟩
  rw [rectangle]
  have equal := congrArg (fun measure : Measure (Space.product source parameter) =>
    measure (Set.product set region)) selection.reconstruction
  rw [reverseSemiproduct_apply_product _ _ _ measurable regionMeasurable] at equal
  exact equal.symm

/-- Two exact disintegrations of the same joint assign almost-everywhere equal
conditional mass to any fixed measurable event under a σ-finite second marginal.
Neither space requires a standard-Borel presentation. -/
public theorem conditional_apply_aeEq (first second : Disintegration joint)
    (finite : SigmaFinite (secondMarginal joint))
    {set : Set alpha} (measurable : source.Measurable set) :
    (secondMarginal joint).AEEq
      (fun input => first.conditional input set) (fun input => second.conditional input set) :=
  (first.conditional_isDensity measurable).ae_eq (second.conditional_isDensity measurable) finite
    (first.conditional.measurable measurable) (second.conditional.measurable measurable)

end Problib.Measure.Measure.Disintegration
